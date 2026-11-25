-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_UniformAssignment
-- name    : PandoraKnapsack_Skipping_UniformAssignment
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:25:06.97827+00:00
-- url     : https://prove2.me/theorems/7dd407de-02c9-4519-96cb-35fa0aebd61c
-- title:
--   Uniform-draw implementation of categorical item assignments
-- statement:
--   Each item reads its own uniform coordinate $u$ and scans an ordered row of choice-time labels. Column $k$ of mass $p_k$ is selected on the half-open interval
--   $$[\sum_{h<k}p_h,\,\sum_{h\le k}p_h).$$
--   The mass for label $(j,t)$ is $x_{ijt}/4$. An unmatched draw leaves the item unassigned.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1, initial independent categorical assignments. Inverse-CDF realization with a single uniform draw per item in the mission machine.

import Definitions.Def_PandoraKnapsack_Skipping_RoundingPayoff

namespace PandoraKnapsack.Skipping

/-- Left edge of the allocation interval for column `k`. -/
noncomputable def cellStart {d : ℕ} (p : Fin d → ℝ) (k : ℕ) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : Fin d => z.val < k), p z

/-- Locate a draw in a row of disjoint half-open allocation intervals.
An unmatched draw, including the right endpoint, leaves the item unassigned. -/
noncomputable def uniformCell {d : ℕ} (p : Fin d → ℝ) (u : ℝ) : Option (Fin d) :=
  Fin.find? (fun k => decide (cellStart p k.val ≤ u ∧ u < cellStart p k.val + p k))

/-- The assignment made by scanning the same ordered choice-time columns for each item.
The item indexed by `i` reads draw number `i`. -/
noncomputable def uniformAssignment {n m T d B : ℕ} (hB : n ≤ B)
    (lab : Fin d → Fin m × Fin (T+1)) (x : LPArray n m)
    (ω : Fin B → unitInterval) : Assignment n m T :=
  fun i => (uniformCell (fun k => x i (lab k).1 (lab k).2.val / 4)
    (ω (i.castLE hB))).map lab

end PandoraKnapsack.Skipping


