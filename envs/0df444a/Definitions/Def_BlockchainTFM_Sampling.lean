-- Prove2me | Definitions.Def_BlockchainTFM_Sampling
-- name    : BlockchainTFM_Sampling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:02.063042+00:00
-- url     : https://prove2.me/theorems/a0251561-195d-4f25-a5bb-b1b59c4e9dfd
-- title:
--   Weighted sampling without replacement: outcome probabilities (24) and inclusion probabilities (25)
-- statement:
--   Fix $n$ users with positive weights $w_1,\dots,w_n$ and total $W=\sum_j w_j$. In $k$ rounds of weighted sampling without replacement, each round draws one not-yet-drawn user with probability proportional to its weight.
--
--   1. **Outcome probability** (24). The probability that the first $t$ rounds produce the sequence of distinct users $(j_1,\dots,j_t)$ is
--   $$\frac{w_{j_1}}{W}\cdot\frac{w_{j_2}}{W-w_{j_1}}\cdots\frac{w_{j_t}}{W-w_{j_1}-\cdots-w_{j_{t-1}}}.$$
--   2. **Inclusion probability** (23), (25). $\delta_t(i)$ is the sum of (24) over all outcomes $(j_1,\dots,j_{t-1},i)$ of distinct users ending with $i$ (the probability that $i$ is drawn in round $t$), and
--   $$a_i=\sum_{t=1}^k\delta_t(i)$$
--   is the probability that user $i$ is drawn in the $k$ rounds.
--
--   Mechanism 3 uses these probabilities with $w_j=e^{mb_j}$ as its allocation rule; for $k=1$ they reduce to the logit shares $w_i/W$.
--
--   **Formalization Note** Outcomes of length $t$ are injective maps $\{1,\dots,t\}\to\{1,\dots,n\}$. When $t>n$ there are none, so for $k\ge n$ every user is drawn with probability $1$, as the paper states in EC.4.4.1 ("If $1\le n\le k$, we have $a_i=1$").
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §6.1 (23)–(25) pp.28–29; EC.4.4.1 p.ec17

import Mathlib

namespace BlockchainTFM

/-- **Probability of a sampling outcome** in weighted sampling without replacement,
arXiv:2209.13099v7, (24), p.29: for distinct users `j₁, …, j_t` (here the injective sequence
`s`) and positive weights `w` with total `W = ∑_j w_j`,
`w_{j₁}/W · w_{j₂}/(W − w_{j₁}) ⋯ w_{j_t}/(W − w_{j₁} − ⋯ − w_{j_{t−1}})`.

**Formalization Note.** Position `u : Fin t` of the sequence is the paper's round `u+1`; its
denominator subtracts the weights of the users drawn in the earlier positions `v < u`. -/
noncomputable def seqProb {n t : ℕ} (w : Fin n → ℝ) (s : Fin t ↪ Fin n) : ℝ :=
  ∏ u : Fin t, w (s u) / (∑ j, w j - ∑ v ∈ Finset.univ.filter (fun v => v < u), w (s v))

/-- **Inclusion probability** in `k`-round weighted sampling without replacement,
arXiv:2209.13099v7, §6.1, (23)–(25), pp.28–29: `a_i = ∑_{t=1}^{k} δ_t(i)`, where `δ_t(i)` is
the probability that user `i` is drawn in round `t`, i.e. the sum of (24) over all sampling
outcomes `(j₁, …, j_{t−1}, i)` of distinct users ending with `i`.

**Formalization Note.** Round `t+1` (for `t ∈ {0, …, k−1}`) is the sum over injective sequences
`s : Fin (t+1) ↪ Fin n` whose last entry is `i`. When `t + 1 > n` there are no such sequences,
so for `k ≥ n` all `n` users are drawn and the inclusion probability is `1`, as in EC.4.4.1
("If `1 ≤ n ≤ k`, we have `a_i = 1`"). -/
noncomputable def inclProb {n : ℕ} (k : ℕ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.range k,
    ∑ s ∈ (Finset.univ : Finset (Fin (t + 1) ↪ Fin n)).filter (fun s => s (Fin.last t) = i),
      seqProb w s

end BlockchainTFM


