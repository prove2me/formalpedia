-- Prove2me | Definitions.Def_CompDesignBFM_singletonMech
-- name    : CompDesignBFM_singletonMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:19.259418+00:00
-- url     : https://prove2.me/theorems/6cfd3d01-4582-4cc2-a851-3b5b1ed6016a
-- title:
--   Singleton branch
-- statement:
--   The **singleton branch** selects, among the agents with $b_i\le B$, the one with the largest value $v(\{i\})$, ties broken by a fixed agent priority, and pays it the whole budget $B$. If no agent is eligible it selects the empty set.
--
--   **Formalization Note** Written as a filter; for an injective priority the filter is the `arg max`, a single agent whenever some agent is eligible.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Mechanism 4.1, steps 4–7, p.23 (PDF 25), and p.21 (PDF 23)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism

namespace CompDesignBFM

open Classical in
/-- The singleton branch (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Mechanism 4.1, steps 4–7, p.23, PDF 25, and p.21, PDF 23): among the
agents with `bᵢ ≤ B` select the one with the largest `v {i}`, ties broken by the agent priority `rho`
(smaller first), and pay it `B`; if no agent is affordable select `∅`.
**Formalization Note.** Written as a filter, so no choice is needed: for injective `rho` the filter is
exactly the `arg max`, a singleton whenever some agent is affordable. -/
noncomputable def singletonMech {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (rho : Fin n → ℕ) : Mechanism n where
  alloc := fun b => Finset.univ.filter fun i =>
    b i ≤ B ∧ ∀ j, b j ≤ B → v {j} < v {i} ∨ (v {j} = v {i} ∧ rho i ≤ rho j)
  pay := fun b i =>
    if b i ≤ B ∧ ∀ j, b j ≤ B → v {j} < v {i} ∨ (v {j} = v {i} ∧ rho i ≤ rho j) then B else 0

end CompDesignBFM


