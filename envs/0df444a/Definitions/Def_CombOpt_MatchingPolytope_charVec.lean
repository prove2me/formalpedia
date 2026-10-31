-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_charVec
-- name    : CombOpt_MatchingPolytope_charVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:22.439152+00:00
-- url     : https://prove2.me/theorems/a4ca6012-0b1a-4c96-8242-974420ca7c29
-- title:
--   The characteristic vector $\chi_M\in\mathbb R^E$ of an edge set
-- statement:
--   For a finite set $E$ and $M\subseteq E$, the **characteristic vector** of $M$ is the vector $\chi_M\in\mathbb R^E$ with
--   $$(\chi_M)_e=\begin{cases}1,& e\in M,\\ 0,& e\notin M.\end{cases}$$
--   For $x\in\mathbb R^E$ and $A\subseteq E$, $x(A)=\sum_{e\in A}x_e$, so $\chi_M(A)=|M\cap A|$.
--
--   Characteristic vectors turn families of edge sets into finite point sets in $\mathbb R^E$, whose convex hulls are the polytopes of the chapter.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.1, p. 199 (PDF p. 207); §2.1, p. 16 (PDF p. 25)

import Mathlib

namespace CombOpt.MatchingPolytope

open Classical in
/-- **The characteristic vector of a set of edges.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.1, p. 199 (PDF p. 207) and §2.1, p. 16 (PDF p. 25): the characteristic vector
`x ∈ ℝ^E` of `M ⊆ E` has `x_e = 1` if `e ∈ M` and `x_e = 0` otherwise. -/
noncomputable def charVec {E : Type*} (M : Finset E) : E → ℝ :=
  fun e => if e ∈ M then 1 else 0

end CombOpt.MatchingPolytope


