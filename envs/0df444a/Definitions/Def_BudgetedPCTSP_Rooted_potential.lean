-- Prove2me | Definitions.Def_BudgetedPCTSP_Rooted_potential
-- name    : BudgetedPCTSP_Rooted_potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T13:15:54.934353+00:00
-- url     : https://prove2.me/theorems/44d8f1bd-5d35-423f-ac43-3aa1b254aa5b
-- title:
--   Definition 1 — the potential π(S) = |S| − 2 Σ_{T ⊊ S} y_T
-- statement:
--   Let $V$ be a finite set and let $y$ assign a real number $y_T$ to every subset $T \subseteq V$ (a dual vector). The **potential** of a set $S \subseteq V$ is
--   $$\pi(S) := |S| - 2 \sum_{T : T \subsetneq S} y_T ,$$
--   where the sum runs over the strict subsets of $S$ only.
--
--   Potentials measure how much of a set's vertex count has not yet been paid for by the duals of its strict subsets; they appear in both the upper bound on the optimum (Theorem 1) and the lower bound on the algorithm's tour (Theorem 2) of the paper.
-- source:
--   Paul, Freund, Ferber, Shmoys & Williamson, Budgeted Prize-Collecting Traveling Salesman and Minimum Spanning Tree Problems, Math. Oper. Res. 2020 (DOI 10.1287/moor.2019.1002), author manuscript p. 4, Definition 1

import Mathlib

namespace BudgetedPCTSP.Rooted

/-- Definition 1 (p. 4) of Paul, Freund, Ferber, Shmoys & Williamson (Math. Oper. Res. 2020):
for a dual vector `y`, which assigns a real value `y T` to every vertex set `T ⊆ V`, the
potential of `S ⊆ V` is `π(S) := |S| - 2 ∑_{T ⊊ S} y_T`, the sum running over the strict
subsets of `S`. -/
noncomputable def potential {V : Type} [DecidableEq V] (y : Finset V → ℝ) (S : Finset V) : ℝ :=
  (S.card : ℝ) - 2 * ∑ T ∈ S.ssubsets, y T

end BudgetedPCTSP.Rooted


