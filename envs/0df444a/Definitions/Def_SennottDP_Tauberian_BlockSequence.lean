-- Prove2me | Definitions.Def_SennottDP_Tauberian_BlockSequence
-- name    : SennottDP_Tauberian_BlockSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T12:57:43.826987+00:00
-- url     : https://prove2.me/theorems/646bef20-88ca-4644-b5bf-c3cb23d0498d
-- title:
--   The 0/1 block sequence of Example A.5.1: q_1 ones, q_1 zeros, q_2 ones, q_2 zeros, …
-- statement:
--   Let $(q_k)_{k \ge 1}$ be a sequence of positive integers and $s_k = \sum_{i=1}^{k} q_i$ ($s_0 = 0$). The **block sequence** $(u_n)_{n \ge 0}$ consists of $q_1$ ones, then $q_1$ zeros, then $q_2$ ones, then $q_2$ zeros, and so on. With indexing from $0$, the $k$-th pair of blocks occupies the positions $2s_{k-1} \le n < 2s_k$, and
--   $$u_n = \begin{cases} 1, & 2 s_{k-1} \le n < 2 s_{k-1} + q_k \text{ for some } k \ge 1,\\ 0, & \text{otherwise.} \end{cases}$$
--   In particular $u_n = 1$ for $0 \le n \le q_1 - 1$.
--
--   It is the sequence of Example A.5.1, used to show that the inequalities of the Tauberian theorem can be strict.
--
--   **Formalization Note** `q : ℕ → ℕ`; the value `q 0` is never used. `blockSum q k` is $s_k$ and `blockSeq q n` is $u_n$ as an element of `ℝ≥0∞`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 286, Example A.5.1 and Fig. A.4

import Mathlib

open scoped ENNReal

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 286, Example A.5.1: `s_k = ∑_{i=1}^k q_i` for a sequence `(q_i)_{i ≥ 1}`
(`s_0 = 0`; the value `q 0` is never used). -/
def blockSum (q : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 k, q i

/-- Sennott (1999), p. 286, Example A.5.1 and Fig. A.4: the `0/1` sequence made of blocks
`q_1` ones, `q_1` zeros, `q_2` ones, `q_2` zeros, …, indexed from `n = 0`.
The `k`-th pair of blocks (`k ≥ 1`) occupies positions `2 s_{k-1} ≤ n < 2 s_k`; its ones are the
positions `2 s_{k-1} ≤ n < 2 s_{k-1} + q_k`. So `u_n = 1` for `0 ≤ n ≤ q_1 - 1`. -/
noncomputable def blockSeq (q : ℕ → ℕ) (n : ℕ) : ℝ≥0∞ := by
  classical
  exact if ∃ k, 1 ≤ k ∧ 2 * blockSum q (k - 1) ≤ n ∧ n < 2 * blockSum q (k - 1) + q k
    then 1 else 0

end SennottDP.Tauberian


