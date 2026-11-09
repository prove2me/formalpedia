-- Prove2me | Definitions.Def_QueryDepthMIS_ivIdx
-- name    : QueryDepthMIS_ivIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:56.640662+00:00
-- url     : https://prove2.me/theorems/c39ba9d3-398b-4518-bc3a-2d3d2e8428c0
-- title:
--   Index of the interval containing a position
-- statement:
--   For a position $p \in \{1, \dots, n\}$, the index $i \in \{1, \dots, b\}$ with $p \in I_i$; for $\alpha > 0$ the intervals partition $\{1, \dots, n\}$, so it is unique. It is used to name $p = p_{i,j}$.
--
--   **Formalization Note** Computed as the largest $i \le b$ with $p \in I_i$; the value is $0$ for $p$ outside $\{1, \dots, n\}$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_Iv
import Definitions.Def_QueryDepthMIS_bNum

set_option autoImplicit false

namespace QueryDepthMIS

/-- The index `i` of the interval `I_i` containing a position `p` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14: "write
p_{i,j} for the j-th position of P ∩ I_i"): the largest `i ≤ b` with `p ∈ I_i`.

**Formalization Note** For `α > 0` the intervals `I₁, …, I_b` partition `{1, …, n}`, so the
index is unique for `p ∈ [1, n]`; outside `[1, n]` the value is `0`. -/
noncomputable def ivIdx (α : ℝ) (n p : ℕ) : ℕ := by
  classical
  exact ((Finset.range (bNum α n + 1)).filter (fun i => p ∈ Iv α n i)).sup id

end QueryDepthMIS


