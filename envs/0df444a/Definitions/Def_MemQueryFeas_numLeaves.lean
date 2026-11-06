-- Prove2me | Definitions.Def_MemQueryFeas_numLeaves
-- name    : MemQueryFeas_numLeaves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:48.538179+00:00
-- url     : https://prove2.me/theorems/292f27db-cb55-4135-9a66-e2717966fb2f
-- title:
--   Number of leaves $N_1\cdots N_P$
-- statement:
--   The skeleton tree has $N_1N_2\cdots N_P$ leaves.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.2, p.10 (PDF p.11)

import Mathlib

namespace MemQueryFeas

/-- **Number of leaves `|V_P| = N_1 ⋯ N_P`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.2, p.10 (PDF p.11): "the skeleton tree has
`N_1 ⋯ N_P` leaves". -/
def numLeaves (N : ℕ → ℕ) (P : ℕ) : ℕ := ∏ p ∈ Finset.range P, N (p + 1)

end MemQueryFeas


