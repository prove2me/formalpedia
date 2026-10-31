-- Prove2me | Definitions.Def_UnbiasedTimeAvg_levelProb
-- name    : UnbiasedTimeAvg_levelProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:18.6241+00:00
-- url     : https://prove2.me/theorems/d1f2a0b1-95fd-4121-a0f9-9c8456aa488b
-- title:
--   The $\bar\nu$-dependent level distribution $(p_l)$ of (3.6)–(3.7)
-- statement:
--   For $k\ge1$ the paper chooses
--   $$p_l=\frac{\bar\nu(k2^{l-2})-\bar\nu(k2^{l-1})}{2^l\,\bar\nu(k)}\quad(l\ge2),\qquad(3.6)$$
--   $$p_1=\Big(1-\sum_{l=2}^\infty p_l\Big)\Big/3,\qquad p_0=2p_1.\qquad(3.7)$$
--   The $p_l$ for $l\ge2$ make the summands of the bounds on $T_k$ and $\mathbb E(Z_k^2)$ in Lemma 3.2 proportional.
--
--   **Formalization Note** The case $l=j+2$ is written with $k2^j$ and $k2^{j+1}$, avoiding natural-number subtraction. That $(p_l)$ is a positive probability distribution is the milestone (3.8).
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.6)–(3.7), p.9

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_nuBar

namespace UnbiasedTimeAvg

/-- **The `ν̄`-dependent level distribution `(p_l)`.** Kahalé, arXiv:2209.09581v1, (3.6)–(3.7),
p.9: "For `l ≥ 2`, set `p_l = (ν̄(k2^{l−2}) − ν̄(k2^{l−1}))/(2^l ν̄(k))` (3.6), and
`p_1 = (1 − Σ_{l=2}^∞ p_l)/3` and `p_0 = 2p_1` (3.7)."

`levelProb ν k l` is `p_l`. The case `l = j + 2` is (3.6) with `k2^{l−2} = k2^j` and
`k2^{l−1} = k2^{j+1}`.

**Formalization Note.** Indexing by `j + 2` avoids natural-number subtraction. The sum
`Σ_{l ≥ 2} p_l` is a real `tsum`; its summability (and the facts that `(p_l)` is a positive
probability distribution) is the milestone (3.8), not part of the definition. -/
noncomputable def levelProb (ν : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 2 * ((1 - ∑' j : ℕ,
      (nuBar ν (k * 2 ^ j) - nuBar ν (k * 2 ^ (j + 1))) / (2 ^ (j + 2) * nuBar ν k)) / 3)
  | 1 => (1 - ∑' j : ℕ,
      (nuBar ν (k * 2 ^ j) - nuBar ν (k * 2 ^ (j + 1))) / (2 ^ (j + 2) * nuBar ν k)) / 3
  | j + 2 => (nuBar ν (k * 2 ^ j) - nuBar ν (k * 2 ^ (j + 1))) / (2 ^ (j + 2) * nuBar ν k)

end UnbiasedTimeAvg


