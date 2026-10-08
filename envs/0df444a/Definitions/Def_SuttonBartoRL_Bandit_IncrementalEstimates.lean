-- Prove2me | Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates
-- name    : SuttonBartoRL_Bandit_IncrementalEstimates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:28:18.967454+00:00
-- url     : https://prove2.me/theorems/6bd3012d-50b2-4988-907f-f7b7d9841673
-- title:
--   Sample-average estimate $Q_n$, trace of one $\bar o_n$ and the unbiased step size $\beta_n$
-- statement:
--   Fix one action of a bandit problem and let $R_1, R_2, \dots$ be the rewards received after its first, second, … selections. After the action has been selected $n-1$ times, its **sample-average estimate** is
--
--   $$
--   Q_n = \frac{R_1 + R_2 + \cdots + R_{n-1}}{n-1}, \qquad n \ge 2,
--   $$
--
--   and before any reward ($n = 1$) the estimate is an arbitrary initial value $Q_1$.
--
--   For a constant step size $\alpha$, the **trace of one** is the sequence
--
--   $$
--   \bar o_0 = 0, \qquad \bar o_n = \bar o_{n-1} + \alpha\,(1 - \bar o_{n-1}) \quad (n > 0),
--   $$
--
--   and the **unbiased constant step size** used to process the $n$-th reward is $\beta_n = \alpha / \bar o_n$.
--
--   These are the objects of the incremental-implementation and nonstationary-tracking sections of the chapter: the sample average and its update rule (2.3), and the step size (2.8)–(2.9) of Exercise 2.7.
--
--   **Formalization Note** Rewards are a sequence $R : \mathbb N \to \mathbb R$ indexed from $1$ (the value at $0$ is never used). `sampleAverage R Q₁ n` returns $Q_1$ for every $n \le 1$; the book only uses $n \ge 1$. The step size $\beta_n = \alpha/\bar o_n$ is a real division, so it equals $0$ if $\bar o_n = 0$; this happens only for $n = 0$ (or for $\alpha = 2$ and even $n$), which the theorems exclude.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §2.4 display defining Q_n, p. 31; Eqs. (2.8)–(2.9), Exercise 2.7, p. 35

import Mathlib

namespace SuttonBartoRL.Bandit

/-- The sample-average estimate `Q_n` of a single action (Sutton & Barto, p. 31): after the action
has been selected `n - 1` times with rewards `R 1, …, R (n - 1)`, `Q_n = (R_1 + ⋯ + R_{n-1}) / (n - 1)`.
Rewards are indexed from `1`. For `n ≤ 1` no reward has been received and the estimate is the
arbitrary initial value `Q₁` (the book's "arbitrary Q₁"; the index `n = 0` is not used by the book). -/
noncomputable def sampleAverage (R : ℕ → ℝ) (Q₁ : ℝ) (n : ℕ) : ℝ :=
  if n ≤ 1 then Q₁ else (∑ i ∈ Finset.Icc 1 (n - 1), R i) / ((n : ℝ) - 1)

/-- The trace of one `ō_n` of Eq. (2.9): `ō_0 = 0` and `ō_n = ō_{n-1} + α (1 - ō_{n-1})` for `n > 0`. -/
noncomputable def traceOfOne (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => traceOfOne α n + α * (1 - traceOfOne α n)

/-- The unbiased constant-step-size step `β_n = α / ō_n` of Eq. (2.8), used to process the `n`-th
reward of an action. -/
noncomputable def unbiasedStepSize (α : ℝ) (n : ℕ) : ℝ :=
  α / traceOfOne α n

end SuttonBartoRL.Bandit


