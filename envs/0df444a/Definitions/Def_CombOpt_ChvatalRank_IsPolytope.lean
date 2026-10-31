-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsPolytope
-- name    : CombOpt_ChvatalRank_IsPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:39.030606+00:00
-- url     : https://prove2.me/theorems/e695056f-d0e0-4954-848b-5a38a464a577
-- title:
--   Polytope
-- statement:
--   A polyhedron $P\subseteq\mathbb R^n$ is a **polytope** if there exist $l,u\in\mathbb R^n$ such that $l\le x\le u$ for all $x\in P$.
--
--   **Formalization Note** The order on `Fin n → ℝ` is componentwise. The empty set is a polytope.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF 212)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsPolyhedron

open Matrix

namespace CombOpt.ChvatalRank

/-- **Polytope.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF 212):
"a polyhedron P ⊆ Rⁿ is a polytope if there exist l, u ∈ Rⁿ such that l ≤ x ≤ u for all x ∈ P."

**Formalization Note.** The empty set is a polytope (it is a polyhedron, and every `l, u` work). -/
def IsPolytope {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  IsPolyhedron P ∧ ∃ l u : Fin n → ℝ, ∀ x ∈ P, l ≤ x ∧ x ≤ u

end CombOpt.ChvatalRank


