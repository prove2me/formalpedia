-- Prove2me | Definitions.Def_FewExperts_alpha
-- name    : FewExperts_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:12.455458+00:00
-- url     : https://prove2.me/theorems/6c062a8a-4e8c-4bbf-97fc-a06a765104eb
-- title:
--   Parameters $r=\log T$, $s=\log N$, $\alpha=1/(2^{10}r(s+\log r))$, $p=1-1/(2^8r)$ and $K=\lfloor 1/\alpha\rfloor$
-- statement:
--   All logarithms are base 2 unless written $\ln$. For $N$ experts and horizon $T$, Section 4 fixes
--
--   $$
--   r=\log T,\qquad s=\log N,\qquad \alpha=\frac{1}{2^{10}\,r\,(s+\log r)},\qquad p=1-\frac{1}{2^{8}r}.
--   $$
--
--   The threshold indices of HarvestGain range over $\{1,\dots,1/\alpha\}$. Since the paper omits floors, the number of levels is
--
--   $$
--   K=\lfloor 1/\alpha\rfloor .
--   $$
--
--   These constants are shared by every statement of the mission.
--
--   **Formalization Note** `lg x = Real.logb 2 x`. Lean's $x/0=0$ makes $\alpha=0$ when $T\le 1$ (or when $s+\log r=0$). Every statement either assumes $\alpha\ell\ge 1$ or takes $N,T$ beyond thresholds, where $\alpha>0$. Using the floor, rather than the ceiling, keeps the top threshold $K\alpha\ell$ at most $\ell$.
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §3, p.13 (PDF p.14) and §4, p.15 (PDF p.16)

import Mathlib

namespace FewExperts

/-- The base-2 logarithm `log x = log₂ x` (p.13: "All logarithms are base 2 unless ln is
written"). -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- `r = log T` (base 2), p.15. -/
noncomputable def rT (T : ℕ) : ℝ := lg T

/-- `s = log N` (base 2), p.15. -/
noncomputable def sN (N : ℕ) : ℝ := lg N

/-- **The parameters `r`, `s`, `α`, `p` of §4 and the number of threshold levels.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §4, p.15 (PDF 16): "Everywhere, let r = log T and s = log N, and set
α = 1/(2¹⁰ r(s + log r)) and p = 1 − 1/(2⁸ r)."

`alpha N T = 1/(2¹⁰ · r · (s + log r))` with `r = log₂ T`, `s = log₂ N`.

**Formalization Note** Real division by zero is `0` in Lean, so `alpha N T = 0` when `T ≤ 1`
or when `s + log r = 0`; every statement of the mission that uses `α` either assumes `αℓ ≥ 1`
or works for `N, T` beyond explicit thresholds, where `α > 0`. -/
noncomputable def alpha (N T : ℕ) : ℝ := 1 / (2 ^ 10 * rT T * (sN N + lg (rT T)))

/-- `p = 1 − 1/(2⁸ r)` (p.15), the parameter of the threshold law (8). For `T ≥ 2` it lies in
`(0, 1)`; for `T ≤ 1` (`r = 0`) it is `1` by Lean's `1/0 = 0`. -/
noncomputable def pT (T : ℕ) : ℝ := 1 - 1 / (2 ^ 8 * rT T)

/-- The number `K = ⌊1/α⌋` of threshold levels: the thresholds of Algorithm 3 range over
`{1, …, 1/α}` (p.16), and the paper omits floors (p.13).

**Formalization Note** The floor (not the ceiling) is used, so that the top threshold
`K α ℓ` is at most `ℓ`, which the proof of Proposition 2 (i) uses ("its threshold is at most
ℓ", p.17). Every occurrence of `1/α` as a number of levels or as an exponent in the paper
(`Pr[r_i ≤ j] = p^{1/α − j}`, Lemma 6's `p^{1/α−1}`) is read with `K` in its place. -/
noncomputable def numLevels (N T : ℕ) : ℕ := ⌊1 / alpha N T⌋₊

end FewExperts


