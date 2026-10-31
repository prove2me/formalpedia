-- Prove2me | Definitions.Def_CombOpt_ChvatalRank_IsPolyhedron
-- name    : CombOpt_ChvatalRank_IsPolyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:43.847015+00:00
-- url     : https://prove2.me/theorems/68adcf02-196a-4f93-a674-08c08e1d4132
-- title:
--   Polyhedron
-- statement:
--   A set $P\subseteq\mathbb R^n$ is a **polyhedron** if it is the solution set of a finite system of linear inequalities, that is, $P=\{x : Ax\le b\}$ for a real $m\times n$ matrix $A$ and $b\in\mathbb R^m$.
--
--   **Formalization Note** $m=0$ gives $\mathbb R^n$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 203 (PDF 211)

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron

open Matrix

namespace CombOpt.ChvatalRank

/-- **Polyhedron.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 203 (PDF 211):
"A polyhedron is the solution set of a finite system of linear inequalities."

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`. `m = 0` gives `ℝⁿ`. -/
def IsPolyhedron {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), P = RobustToDynamics.polyhedron A b

end CombOpt.ChvatalRank


