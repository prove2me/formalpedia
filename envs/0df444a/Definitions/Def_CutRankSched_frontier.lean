-- Prove2me | Definitions.Def_CutRankSched_frontier
-- name    : CutRankSched_frontier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:33:44.936589+00:00
-- url     : https://prove2.me/theorems/754dad4a-af27-44a6-a6e8-316d893cf4f5
-- title:
--   Residual-conflict frontier $F^\circ_k$
-- statement:
--   For the cut after the first $k$ events ($0 \le k \le n$), the **residual-conflict frontier** is
--   $$
--   F^\circ_k = \{\, j \le k : \exists\, h > k,\ \{j, h\} \in E(X^\circ) \,\},
--   $$
--   the processed events that still have a residual conflict with some unprocessed event.
--
--   **Formalization Note** With 0-based events, $j \le k$ and $h > k$ become `j.val < k` and `k ≤ h.val`.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.3, p.5

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Residual

set_option autoImplicit false

namespace CutRankSched

/-- The residual-conflict frontier `F°_k = {j ≤ k : ∃ h > k, {j, h} ∈ E(X°)}` at the cut after
the first `k` events (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.3, p.5).

**Formalization Note** With 0-based events the paper's `j ≤ k` and `h > k` are `j.val < k` and
`k ≤ h.val`. -/
noncomputable def frontier (I : Instance) (k : ℕ) : Finset (Fin I.n) := by
  classical
  exact Finset.univ.filter fun j => j.val < k ∧ ∃ h : Fin I.n, k ≤ h.val ∧ Residual I j h

end CutRankSched


