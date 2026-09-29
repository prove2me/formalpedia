-- Prove2me | Definitions.Def_CandesTao_LowerBound_SamplingConditions
-- name    : CandesTao_LowerBound_SamplingConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:43:50.447987+00:00
-- url     : https://prove2.me/theorems/33dee918-0b8a-45a1-a573-747568b4342c
-- title:
--   Sampling conditions (I.20) and (I.21) of Theorem 1.7
-- statement:
--   Fix integers $n, m, r$ and reals $\mu_0, \delta$, and write $\log$ for the natural logarithm. The two sampling conditions of the lower bound of Candès and Tao are
--
--   $$m \ge n^2\left(1 - e^{-\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right)}\right) \qquad \text{(I.20)}$$
--
--   and
--
--   $$m \ge (1-\epsilon)\,\mu_0 n r\log\left(\frac{n}{2\delta}\right), \qquad \epsilon := \frac12\,\frac{\mu_0 r}{n}\log\left(\frac{n}{2\delta}\right). \qquad \text{(I.21)}$$
--
--   Here $m$ is the expected number of observed entries of an $n\times n$ matrix, $r$ a rank bound, $\mu_0$ an incoherence parameter and $\delta$ a failure probability. Theorem 1.7 states that when either condition fails, recovery from the observed entries cannot be guaranteed with probability better than $1-\delta$. Condition (I.21) is the easier-to-read form: for the theorem's parameters, (I.20) implies (I.21).
--
--   **Formalization Note** The file defines three objects: `SamplingConditionI20 n m r μ₀ δ`, `epsilonI21 n r μ₀ δ` (the quantity $\epsilon$) and `SamplingConditionI21 n m r μ₀ δ`, with $m$, $n$, $r$ cast to $\mathbb{R}$ and `Real.log`, `Real.exp`. The definitions carry no hypotheses on the parameters; the theorems that use them impose the ranges of Theorem 1.7.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2058, Theorem 1.7, Eqs. (I.20), (I.21) and the definition of ε

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CandesTao.LowerBound

/-- Condition (I.20) of Candès–Tao Theorem 1.7 for `n × n` matrices, `m` samples,
rank bound `r`, incoherence parameter `μ₀` and failure level `δ`:
`m ≥ n² (1 - exp(-(μ₀ r / n) log(n / (2δ))))`, with the natural logarithm. -/
def SamplingConditionI20 (n m r : ℕ) (μ₀ δ : ℝ) : Prop :=
  (m : ℝ) ≥ (n : ℝ) ^ 2 * (1 - Real.exp (-(μ₀ * r / n) * Real.log (n / (2 * δ))))

/-- The quantity `ε := ½ (μ₀ r / n) log(n / (2δ))` of Candès–Tao Theorem 1.7. -/
noncomputable def epsilonI21 (n r : ℕ) (μ₀ δ : ℝ) : ℝ :=
  (1 / 2) * (μ₀ * r / n) * Real.log (n / (2 * δ))

/-- Condition (I.21) of Candès–Tao Theorem 1.7:
`m ≥ (1 - ε) μ₀ n r log(n / (2δ))` with `ε = epsilonI21 n r μ₀ δ`. -/
def SamplingConditionI21 (n m r : ℕ) (μ₀ δ : ℝ) : Prop :=
  (m : ℝ) ≥ (1 - epsilonI21 n r μ₀ δ) * μ₀ * n * r * Real.log (n / (2 * δ))

end CandesTao.LowerBound


