-- Prove2me | Definitions.Def_MaxEntTSP_Main_OJoin
-- name    : MaxEntTSP_Main_OJoin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:07.73928+00:00
-- url     : https://prove2.me/theorems/9ebd24c1-ea35-4267-9268-2db375bdefea
-- title:
--   The O-join cut relaxation
-- statement:
--   In a finite graph with edge set $F$, an **$O$-join** is an edge set $J\subseteq F$ whose odd-degree vertices are exactly $O$; this concept is reused from the published `MetricGenerators.FewComponents.TJoin` definition. A nonnegative edge vector $y$ is feasible for the cut relaxation when
--   $$y(\delta_F(S))\ge1\qquad\text{for every }S\text{ with }|S\cap O|\text{ odd}.$$
--
--   These are the primal objects of the Edmonds–Johnson proposition used to bound the parity correction of a sampled tree.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 6 (PDF 8), Proposition 2.3 and LP (3)

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Cuts

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- The cut formulation (3) of the `O`-join polyhedron. -/
def OJoinFeasible {m : ℕ} (F : Finset (Sym2 (Fin m))) (O : Finset (Fin m))
    (y : Sym2 (Fin m) → ℝ) : Prop :=
  (∀ e ∈ F, 0 ≤ y e) ∧
  ∀ S : Finset (Fin m), Odd (S ∩ O).card → 1 ≤ ∑ e ∈ cutEdges F S, y e

end MaxEntTSP.Main


