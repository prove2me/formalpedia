-- Prove2me | Definitions.Def_QueryDepthMIS_jIdx
-- name    : QueryDepthMIS_jIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:33:45.308781+00:00
-- url     : https://prove2.me/theorems/67332760-5c13-4041-8f67-9f7c2093ff29
-- title:
--   In-interval index $j$ of $p = p_{i,j}$
-- statement:
--   For a position $p$ of $P$ lying in $I_i$, the index $j$ such that $p$ is the $j$-th position of $P \cap I_i$ (counting from $1$), i.e. the number of positions of $P \cap I_i$ that are at most $p$. Thus $p = p_{i,j}$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_ivIdx

set_option autoImplicit false

namespace QueryDepthMIS

/-- The index `j` with `p = p_{i,j}`, i.e. `p` is the `j`-th position of `P ∩ I_i` (1-based),
where `I_i` is the interval containing `p` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14): the number of positions of
`P ∩ I_i` that are at most `p`. -/
noncomputable def jIdx (α : ℝ) (n : ℕ) (P : List ℕ) (p : ℕ) : ℕ :=
  ((P.toFinset ∩ Iv α n (ivIdx α n p)).filter (fun x => x ≤ p)).card

end QueryDepthMIS


