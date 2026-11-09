-- Prove2me | Definitions.Def_QueryDepthMIS_prot
-- name    : QueryDepthMIS_prot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:39:16.042912+00:00
-- url     : https://prove2.me/theorems/088f13f4-84b4-458b-984f-302a96290274
-- title:
--   Protected sets $P_1 = \emptyset$, $P_k = B_{k-1}$
-- statement:
--   The protected set of the $k$-th path position is
--   $$
--   P_1 = \emptyset, \qquad P_k = B_{k-1} \quad (2 \le k \le L).
--   $$
--   The hop lemmas are applied with these sets in the role of $P_1, P_2$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_block

set_option autoImplicit false

namespace QueryDepthMIS

/-- The protected sets (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14): "Define P₁ = ∅, P_k = B_{k−1} (2 ≤ k ≤ L)."

**Formalization Note** `k` is 1-based; `prot α n P k` is used for `1 ≤ k ≤ L`. -/
noncomputable def prot (α : ℝ) (n : ℕ) (P : List ℕ) (k : ℕ) : Finset ℕ :=
  if k ≤ 1 then ∅ else block α n P (k - 1)

end QueryDepthMIS


