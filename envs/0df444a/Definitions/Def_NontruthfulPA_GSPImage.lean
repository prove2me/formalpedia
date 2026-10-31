-- Prove2me | Definitions.Def_NontruthfulPA_GSPImage
-- name    : NontruthfulPA_GSPImage
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:19.514981+00:00
-- url     : https://prove2.me/theorems/84a6aacc-79e6-4f47-aaf0-ad071b9b1cb2
-- title:
--   The $\alpha$-GSP image $b^S$ of an $\alpha$-VCG profile (Lemma 2)
-- statement:
--   For a sorted bid profile $b$ and $\alpha \in \mathbb R^k_\ge$, Lemma 2 defines $b^S \in \mathbb R^n$ by
--   $$b^S_i = \begin{cases} b^S_2 & \text{if } i = 1, \\ p^V_{i-1}(b)/\alpha_{i-1} & \text{if } i \in \{2, \dots, k+1\} \text{ and } \alpha_{i-1} > 0, \\ 0 & \text{otherwise,} \end{cases}$$
--   where $p^V_{i-1}(b)$ is the $\alpha$-VCG payment of the bidder in position $i-1$. Under the $\alpha$-GSP mechanism the profile $b^S$ yields the same allocation and the same payments as $b$ under the $\alpha$-VCG mechanism.
--
--   **Formalization Note** Bidders are 0-based: index $m \in \{1, \dots, k\}$ with $\alpha_{m-1} > 0$ gets $p^V_{m-1}(b)/\alpha_{m-1}$, other indices $m \ge 1$ get $0$, and index $0$ copies index $1$. For $n = 1$ the paper's $b^S_2$ does not exist; the formula for index $1$ is used, and it gives $0$.
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, Lemma 2, p.13 (definition of b^S)

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- **The α-GSP image `b^S` of an α-VCG profile**, Dütting–Fischer–Parkes, arXiv:1602.07593v4,
Lemma 2, p.13: for all `i ∈ {1, …, n}`,
`b^S_i = b^S_2` if `i = 1`; `b^S_i = p^V_{i−1}(b) / α_{i−1}` if `i ∈ {2, …, k+1}` and
`α_{i−1} > 0`; and `b^S_i = 0` otherwise.

**Formalization Note.** 0-based: for `m ∈ {1, …, k}` with `0 < α (m−1)`, the entry at index `m`
is `payV k α (padBids b) (m−1) / α (m−1)`, the α-VCG payment of the bidder at rank `m − 1` under
the sorted profile `b` divided by `α (m−1)`; other indices `m ≥ 1` get `0`; index `0` copies the
value of index `1`. For `n = 1` the paper's `b^S_2` does not exist; the same formula (index 1)
is used, and it gives `0` there since `k ≤ 1` and the only payment is `0`. -/
noncomputable def gspImage {n : ℕ} (k : ℕ) (α : ℕ → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  let f : ℕ → ℝ := fun m =>
    if 1 ≤ m ∧ m ≤ k ∧ 0 < α (m - 1) then payV k α (padBids b) (m - 1) / α (m - 1) else 0
  fun i => if (i : ℕ) = 0 then f 1 else f i

end NontruthfulPA


