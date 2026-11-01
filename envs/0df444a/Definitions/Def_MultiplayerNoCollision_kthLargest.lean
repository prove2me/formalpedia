-- Prove2me | Definitions.Def_MultiplayerNoCollision_kthLargest
-- name    : MultiplayerNoCollision_kthLargest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:18.88226+00:00
-- url     : https://prove2.me/theorems/9d48b19c-8ac2-414e-ae0b-bd45de88e6ae
-- title:
--   Sorted means $\mu_{(1)}\ge\dots\ge\mu_{(K)}$, the gap $\Delta=\mu_{(m)}-\mu_{(m+1)}$, the benchmark and the best $m$ arms
-- statement:
--   For a vector $\mu=(\mu_1,\dots,\mu_K)$ of reals, let $\mu_{(1)}\ge\mu_{(2)}\ge\dots\ge\mu_{(K)}$ be its entries sorted in decreasing order (with multiplicity). The paper assumes, "by relabeling the arms if necessary", that $\mu_1\ge\dots\ge\mu_K$; here the means are not relabeled, and the sorted values are computed instead.
--
--   1. `kthLargest mu k` is $\mu_{(k+1)}$ (0-based $k$).
--   2. The **gap** is
--   $$\Delta=\mu_{(m)}-\mu_{(m+1)}.$$
--   3. The **benchmark** of the regret is $\sum_{k=1}^{m}\mu_{(k)}$, the sum of the $m$ largest means.
--   4. The **best $m$ arms** are $\{i:\mu_i>\mu_{(m+1)}\}$; when $\Delta>0$ this set has exactly $m$ elements.
--
--   These quantities depend only on the multiset of values, not on the labeling, which the players do not know.
--
--   **Formalization Note** The sorted values come from Mathlib's ascending sort `Tuple.sort`. For $k\ge K$ the index truncates (the value is the minimum); every use has $k\le m<K$.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §1.1, p.3 (relabeling), p.4 (∆ := µ_m − µ_{m+1}), (2) p.3 (benchmark); §3, p.9 and Algorithm 1, line 10, p.10 (best m arms)

import Mathlib

namespace MultiplayerNoCollision

open Finset

/-- **The sorted means.** Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, p.3: "We may assume, by
relabeling the arms if necessary, that `µ_1 ≥ ··· ≥ µ_K`."

`kthLargest mu k` is the `(k+1)`-th largest entry of `mu : Fin K → ℝ` (0-based `k`), counted with
multiplicity: `kthLargest mu 0 = max_i mu_i`, …, `kthLargest mu (K−1) = min_i mu_i`. The paper's
`µ_k` after relabeling is `kthLargest mu (k − 1)`.

**Formalization Note.** Computed from Mathlib's ascending sort `Tuple.sort mu`: the `(k+1)`-th largest
entry is the entry at ascending position `K − 1 − k`. For `k ≥ K` the index truncates to `0` (the
minimum); every use in this mission has `k ≤ m < K`. The value does not depend on the labeling of
the arms, and `mu` is never assumed sorted. -/
noncomputable def kthLargest {K : ℕ} (mu : Fin K → ℝ) (k : ℕ) : ℝ :=
  if h : 0 < K then mu (Tuple.sort mu ⟨K - 1 - k, by omega⟩) else 0

/-- **The gap** `∆ := µ_m − µ_{m+1}` between the `m`-th and the `(m+1)`-th largest means
(Lugosi, Mehrabian, arXiv:1808.08416v2, p.4). Needs `K ≥ m + 1` to be meaningful. -/
noncomputable def gap {K : ℕ} (mu : Fin K → ℝ) (m : ℕ) : ℝ :=
  kthLargest mu (m - 1) - kthLargest mu m

/-- **The benchmark** `∑_{i ∈ [m]} µ_i` of the regret (2) (Lugosi, Mehrabian, arXiv:1808.08416v2,
p.3), the sum of the `m` largest means. -/
noncomputable def topSum {K : ℕ} (mu : Fin K → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range m, kthLargest mu k

/-- **The best `m` arms**: the arms whose value strictly exceeds the `(m+1)`-th largest value
(Lugosi, Mehrabian, arXiv:1808.08416v2, p.9, "a list `G ⊆ [K]` of `m` arms with the highest
means", and Algorithm 1, line 10, p.10, `Best-m-arms ← {i_1, …, i_m}`).

**Formalization Note.** When `gap mu m > 0` this set has exactly `m` elements and equals
`{i_1, …, i_m}` for every tie-breaking of the sort. -/
noncomputable def topSet {K : ℕ} (mu : Fin K → ℝ) (m : ℕ) : Finset (Fin K) :=
  open Classical in univ.filter fun i => kthLargest mu m < mu i

end MultiplayerNoCollision


