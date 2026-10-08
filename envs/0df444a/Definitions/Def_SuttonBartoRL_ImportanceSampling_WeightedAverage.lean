-- Prove2me | Definitions.Def_SuttonBartoRL_ImportanceSampling_WeightedAverage
-- name    : SuttonBartoRL_ImportanceSampling_WeightedAverage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:16:20.293309+00:00
-- url     : https://prove2.me/theorems/8392358b-16a3-4367-a243-901278a8f0c8
-- title:
--   Weighted average $V_n$ (5.7) and its incremental update (5.8)
-- statement:
--   Let $G_1, G_2, \dots$ be returns with weights $W_1, W_2, \dots$ (for example importance-sampling ratios). The **weighted average** of the first $n-1$ returns is
--
--   $$
--   V_n = \frac{\sum_{k=1}^{n-1} W_k G_k}{\sum_{k=1}^{n-1} W_k}, \qquad n \ge 2 .
--   $$
--
--   The **incremental estimate** starts from an arbitrary $V_1$ and the cumulative weight $C_0 = 0$, and sets
--
--   $$
--   V_{n+1} = V_n + \frac{W_n}{C_n}\bigl[G_n - V_n\bigr] \quad (n \ge 1), \qquad C_{n+1} = C_n + W_{n+1}.
--   $$
--
--   This is the weighted-importance-sampling update used by the off-policy Monte Carlo prediction algorithm of the chapter.
--
--   **Formalization Note** Sequences are indexed from $1$; index $0$ of the incremental estimate is set to $V_1$ and never used. Divisions are real divisions, which return $0$ on a zero denominator; the theorem about these definitions assumes $W_1 > 0$ and $W_k \ge 0$, so no denominator it uses is zero.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.6, Eqs. (5.7)–(5.8), p. 109

import Mathlib

namespace SuttonBartoRL.ImportanceSampling

/-- §5.6, p. 109: the cumulative sum of the weights, `C_0 = 0` and `C_{n+1} = C_n + W_{n+1}`, for
weights `W_1, W_2, …` (the value `W 0` is never used). -/
def cumWeight (W : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => cumWeight W n + W (n + 1)

/-- §5.6, p. 109, Eq. (5.8): the incremental weighted-average estimate, `V_1` arbitrary and
`V_{n+1} = V_n + (W_n / C_n) (G_n − V_n)` for `n ≥ 1`, for returns `G_1, G_2, …` with weights
`W_1, W_2, …`. The index `0` is not used by the book; its value is set to `V_1`. -/
noncomputable def incrementalEstimate (W G : ℕ → ℝ) (V₁ : ℝ) : ℕ → ℝ
  | 0 => V₁
  | 1 => V₁
  | n + 2 => incrementalEstimate W G V₁ (n + 1) +
      W (n + 1) / cumWeight W (n + 1) * (G (n + 1) - incrementalEstimate W G V₁ (n + 1))

/-- §5.6, p. 109, Eq. (5.7): the weighted average
`V_n = (Σ_{k=1}^{n-1} W_k G_k) / (Σ_{k=1}^{n-1} W_k)` of the first `n - 1` returns, `n ≥ 2`. -/
noncomputable def weightedAverage (W G : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 (n - 1), W k * G k) / ∑ k ∈ Finset.Icc 1 (n - 1), W k

end SuttonBartoRL.ImportanceSampling


