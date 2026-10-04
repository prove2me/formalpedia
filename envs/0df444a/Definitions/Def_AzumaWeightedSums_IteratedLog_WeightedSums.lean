-- Prove2me | Definitions.Def_AzumaWeightedSums_IteratedLog_WeightedSums
-- name    : AzumaWeightedSums_IteratedLog_WeightedSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:06:47.579316+00:00
-- url     : https://prove2.me/theorems/a92938e8-a00e-420d-b8e4-277a85ade149
-- title:
--   Weighted sums $S_n$, squared weight sums $D_n^2$ and the maximal sum $S_n^*$
-- statement:
--   Fix real random variables $(x_k)_{k\ge1}$ and a real sequence $(b_k)_{k\ge1}$ of weights (of any sign). Three objects are defined:
--
--   1. the **weighted partial sum** $S_n=\sum_{k=1}^n b_kx_k$, with $S_0=0$;
--   2. the **sum of squared weights** $D_n^2=\sum_{k=1}^n b_k^2$;
--   3. the **maximal partial sum**
--   $$
--   S_n^*(\omega)=\max_{1\le m\le n}\Big|\sum_{k=1}^m b_kx_k(\omega)\Big| .
--   $$
--
--   These are the quantities of §2 (Lemma 2) and §4 (Theorem 2) of Azuma's paper, where the weights are called $(b_k)$ in the lemmas and $(a_n)$ in the theorem.
--
--   **Formalization Note** $S_n^*$ is computed as the maximum over $0\le m\le n$; the extra term $|S_0|=0$ does not change the maximum for $n\ge1$ and gives $S_0^*=0$. Indices start at $1$; the values $b_0$ and $x_0$ are never used.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), https://doi.org/10.2748/tmj/1178243286, p. 358, Lemma 2 (S_n^*), and p. 362, §4 (D_n, S_n)

import Mathlib

namespace AzumaWeightedSums.IteratedLog

/-- The weighted partial sum `S_n = b_1 x_1 + ⋯ + b_n x_n` (Azuma 1967, §2 and §4),
indexed from `1`; `S_0 = 0`. -/
noncomputable def weightedSum {Ω : Type*} (b : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, b k * x k ω

/-- The sum of squared weights `D_n² = b_1² + ⋯ + b_n²` (Azuma 1967, §4, p. 362). -/
noncomputable def sqWeightSum (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, b k ^ 2

/-- The maximal partial sum `S_n^*(ω) = max_{1 ≤ m ≤ n} |b_1 x_1(ω) + ⋯ + b_m x_m(ω)|`
(Azuma 1967, Lemma 2, p. 358). The maximum is taken over `0 ≤ m ≤ n`; the extra term
`m = 0` is `|S_0| = 0`, which does not change the maximum for `n ≥ 1`, and makes
`S_0^* = 0`. -/
noncomputable def maxAbsWeightedSum {Ω : Type*} (b : ℕ → ℝ) (x : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun m => |weightedSum b x m ω|)

end AzumaWeightedSums.IteratedLog


