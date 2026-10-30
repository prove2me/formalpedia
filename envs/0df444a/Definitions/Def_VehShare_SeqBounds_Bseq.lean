-- Prove2me | Definitions.Def_VehShare_SeqBounds_Bseq
-- name    : VehShare_SeqBounds_Bseq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:38.055992+00:00
-- url     : https://prove2.me/theorems/d440fd60-a9a3-4f03-9edb-eec2a87f6626
-- title:
--   The lower-bound sequence $B^j_i$
-- statement:
--   Fix a number of locations $N$ and a workload $W\in\mathbb R$. The sequence $B^j_i=B^j_i(W)$, indexed by a number of vehicles $j$ and an iteration count $i$, is defined by
--
--   $$
--   B^j_0=0,\qquad B^j_{i}=\frac{j}{N+j-1+W\big(1-B^{j-1}_{i-1}\big)}\quad(i\ge1).
--   $$
--
--   With $W=\lambda/\mu=\sum_{(i,j)\in\mathcal A}\Lambda_{ij}q^s_{ij}/\mu_{ij}$ it is the paper's $B^K_i(q^s)$, and with $W=\Lambda/\mu$ (all $q^s_{ij}$ replaced by $1$) its $B^K_i=B^K_i(\mathbf 1)$ (Theorem 2, p. 9, and p. 10). Iterating the availability recursion (5) $i$ times from the value $0$ gives $B^K_i(q^s)$, a lower bound on the availability $\alpha(K)$.
--
--   **Formalization Note** The paper sets $B^j_0=0$ for $j=1,\dots,K$; the definition also sets $B^0_0=0$, which the paper's proof uses ($B^1_1=1/(N+\Lambda/\mu)$). The denominator is computed in the reals; the upper index $j-1$ is natural-number subtraction, exact in the paper's range $1\le i\le j$. Values with $i>j$ are not used by any statement.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, Theorem 2, p. 9; proof of Theorem 2, p. 10

import Mathlib

namespace VehShare.SeqBounds

/-- **The sequence of lower bounds `B^j_i`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), Theorem 2, p. 9, and its proof, p. 10: "`B^K_i(q^s) = K/(N+K−1+λ/µ(1−B^{K−1}_{i−1}(q^s)))`
... `B^j_0 = 0` for all `j = 1, 2, ···, K`".

For a number of locations `N` and a workload `W`, `Bseq N W j 0 = 0` and
`Bseq N W j (i + 1) = j / (N + j − 1 + W (1 − Bseq N W (j − 1) i))`.
The paper's `B^K_i(q^s)` is `Bseq N (λ/μ) K i` with `λ/μ` the workload of `q^s`, and its
`B^K_i = B^K_i(𝟏)` is `Bseq N (Λ/μ) K i`.

**Formalization Note.** Reading 9: `B^j_0 = 0` is taken for every `j`, including `j = 0`
(the paper's proof uses `B^1_1 = 1/(N + Λ/μ)`, i.e. `B^0_0 = 0`). The denominator is computed in
`ℝ` after casting (`(N : ℝ) + j − 1`); the upper index `j − 1` of the recursive call is natural
subtraction, which is exact in the paper's range `1 ≤ i ≤ j`. Values with `i > j` are never used by
the theorems that cite the paper's ranges. -/
noncomputable def Bseq (N : ℕ) (W : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | j, i + 1 => (j : ℝ) / ((N : ℝ) + (j : ℝ) - 1 + W * (1 - Bseq N W (j - 1) i))

end VehShare.SeqBounds


