-- Prove2me | Definitions.Def_ConsiderThenChoose_dpTime
-- name    : ConsiderThenChoose_dpTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:34:08.687449+00:00
-- url     : https://prove2.me/theorems/c2a77ab9-6fa8-4d39-8fd6-69b921d7bc05
-- title:
--   Operation count $(NK + K)\,|\mathcal S|$ of the dynamic program
-- statement:
--   The dynamic program runs in two passes: it first builds the computational tree, spending at most $NK$ operations per node (updating the graph, computing the new connected components, and checking whether each new subproblem is already in the tree), and then solves the subproblems backwards, spending $K$ operations per node on the recursion. Its operation count is
--
--   $$
--   \mathrm{dpTime}(C) = (N K + K)\, |\mathcal S|.
--   $$
--
--   This is the paper's accounting of the running time, $O(NK \cdot |\mathcal S|)$, which it then reduces to bounding $|\mathcal S|$.
--
--   **Formalization Note** The paper fixes no machine model; its running-time statements rest on this operation count. Any cost within a constant factor of $(NK + K)|\mathcal S|$ gives the same asymptotic statements in Theorem 1.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Complexity analysis", p. 14

import Mathlib
import Definitions.Def_ConsiderThenChoose_stateSpace

namespace ConsiderThenChoose

/-- **Operation count of the two-pass dynamic program.** Aouad, Farias and Levi, Management
Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "Complexity analysis", unnumbered, p. 14:
"the running time complexity is O(NK · |S|). Indeed, building each node of the computational
tree requires at most O(NK) operations. [...] Then, the subproblems are solved backwards using
the recursive formula with a total running time complexity of O(K · |S|), taking O(K)
operations at each step to solve Equation (1)."

`dpTime C = (N·K + K) · |𝒮|`: `N·K` operations per state to build the computational tree and
`K` operations per state for the backward induction.

**Formalization Note** (Reading 3.) The paper proves no theorem about a machine model; its
running-time statements rest on this operation count, which it then reduces to `|𝒮|`. Any cost
within a constant factor of `(N·K + K)·|𝒮|` gives the same asymptotic statements. -/
noncomputable def dpTime {N K : ℕ} (C : Fin K → Finset (Fin N)) : ℕ :=
  (N * K + K) * (stateSpace C).ncard

end ConsiderThenChoose


