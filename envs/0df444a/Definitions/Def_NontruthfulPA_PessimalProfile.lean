-- Prove2me | Definitions.Def_NontruthfulPA_PessimalProfile
-- name    : NontruthfulPA_PessimalProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:17:19.84213+00:00
-- url     : https://prove2.me/theorems/0663a0cb-91b3-4859-b474-f5f4b207bb39
-- title:
--   The bidder-pessimal profile (26)
-- statement:
--   Given values $v_1 \ge \dots \ge v_n$, position vectors $\alpha, \beta$ and a sorted bid profile $b$, the **bidder-pessimal profile** $\hat b$ of the proof of Lemma 1 is defined by $\hat b_1 = b_1$ and, for $i \in \{2, \dots, n\}$,
--   $$\hat b_i = \begin{cases} \min\Big(\hat b_{i-1},\ \dfrac{(\beta_{i-1} - \beta_i)\, v_{i-1}}{\alpha_{i-1} - \alpha_i}\Big) & \text{if } \alpha_{i-1} \ne \alpha_i, \\ \hat b_{i-1} & \text{otherwise.} \end{cases} \tag{26}$$
--
--   It raises every bid below the top one as far as the two upper bounds of an efficient $\alpha$-VCG equilibrium allow. Lemma 1 shows that it is an envy-free efficient equilibrium.
--
--   **Formalization Note** Bidders are 0-based. The recursion is built left to right and uses the new value $\hat b_{i-1}$. Only $b_1$ of the input profile enters.
-- source:
--   Dütting, Fischer & Parkes, Non-Truthful Position Auctions Are More Robust to Misspecification, arXiv:1602.07593v4, proof of Lemma 1, (26), p.12

import Mathlib
import Definitions.Def_NontruthfulPA_Model

namespace NontruthfulPA

/-- The recursion (26) of arXiv:1602.07593v4, proof of Lemma 1, p.12, on `ℕ`, 0-based: start from `b0`, and at step
`m + 1` cap the previous bid by `(β m − β (m+1)) w m / (α m − α (m+1))` when
`α m ≠ α (m+1)`, else copy it. -/
noncomputable def pessimalAux (α β w : ℕ → ℝ) (b0 : ℝ) : ℕ → ℝ
  | 0 => b0
  | m + 1 =>
    if α m ≠ α (m + 1) then
      min (pessimalAux α β w b0 m) ((β m - β (m + 1)) * w m / (α m - α (m + 1)))
    else pessimalAux α β w b0 m

/-- **The bidder-pessimal profile (26)**, Dütting–Fischer–Parkes, arXiv:1602.07593v4, proof of
Lemma 1, p.12: built from a sorted profile `b`, with `b̂_1 = b_1` and, for
`i ∈ {2, …, n}`,
`b̂_i = min(b̂_{i−1}, (β_{i−1} − β_i) v_{i−1} / (α_{i−1} − α_i))` if `α_{i−1} ≠ α_i`, and
`b̂_i = b̂_{i−1}` otherwise.

**Formalization Note.** Bidders are 0-based (`Fin n`), so bidder `i` here is the paper's
`i + 1`. The recursion uses the new value `b̂_{i−1}` on the right-hand side, as the page's
"Increasing each of these bids as much as possible" builds the profile left to right. Only
`b_1` (here `b 0`) of the input profile is used. -/
noncomputable def pessimal {n : ℕ} (α β : ℕ → ℝ) (v b : Fin n → ℝ) : Fin n → ℝ := fun i =>
  pessimalAux α β (padBids v) (b ⟨0, Nat.zero_lt_of_lt i.isLt⟩) i

end NontruthfulPA


