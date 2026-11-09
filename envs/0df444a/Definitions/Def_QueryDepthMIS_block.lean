-- Prove2me | Definitions.Def_QueryDepthMIS_block
-- name    : QueryDepthMIS_block
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:51.429927+00:00
-- url     : https://prove2.me/theorems/b56bfd42-964c-46ee-9a8e-c54a9487baa3
-- title:
--   Blocks $B_k$ of the path positions
-- statement:
--   For each occupied interval $I_i$, sort $I_{i-1} \setminus P$ increasingly and take its first $s_i\ell_i$ positions, partitioned in order into $s_i$ blocks of size $\ell_i$. The $j$-th block is assigned to $p_{i,j}$ and called $B_k$ when $p_k = p_{i,j}$. Thus $B_1 < \cdots < B_L$.
--
--   **Formalization Note** $k$ is 1-based ($p_k$ is the $k$-th entry of $P$); $B_k$ is the set of entries of the sorted list of $I_{i-1} \setminus P$ with 0-based index in $[(j-1)\ell_i, j\ell_i)$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_ell
import Definitions.Def_QueryDepthMIS_jIdx

set_option autoImplicit false

namespace QueryDepthMIS

/-- The block `B_k` of the `k`-th path position (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14): "For each fixed i with
s_i > 0, we associate each p_k ∈ I_i with a protected set P_k constructed as follows. First, sort
I_{i−1} \ P and take its first s_iℓ_i positions, partitioned in order into s_i blocks of size ℓ_i.
Assign the j-th block to p_{i,j} and call it B_k when p_k = p_{i,j}."

For `P = [p₁, …, p_L]` and `1 ≤ k ≤ L`, with `p_k ∈ I_i` and `p_k = p_{i,j}`: the entries of
the increasingly sorted list of `I_{i−1} \ P` with 0-based index in `[(j − 1)ℓ_i, jℓ_i)`.

**Formalization Note** `k` is 1-based (`p_k = P[k − 1]`). -/
noncomputable def block (α : ℝ) (n : ℕ) (P : List ℕ) (k : ℕ) : Finset ℕ :=
  let p := P.getD (k - 1) 0
  let i := ivIdx α n p
  let j := jIdx α n P p
  let l := ell α n P i
  ((((Iv α n (i - 1) \ P.toFinset).sort (· ≤ ·)).drop ((j - 1) * l)).take l).toFinset

end QueryDepthMIS


