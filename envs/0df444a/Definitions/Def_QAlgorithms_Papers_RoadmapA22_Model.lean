-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA22_Model
-- name    : QAlgorithms_Papers_RoadmapA22_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:15.418516+00:00
-- url     : https://prove2.me/theorems/ae4ee9fa-480e-49a1-be1a-78ed5376f6b1
-- title:
--   Quantum speedup of Monte Carlo methods: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Quantum speedup of Monte Carlo methods, arXiv:1504.06987v3, https://arxiv.org/abs/1504.06987v3. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BoundedMeanEstimation
noncomputable section

namespace QAlgorithms.Papers.RoadmapA22

/-- Probability that Algorithm 1's median is within `radius` of the output mean.

Montanaro, arXiv:1504.06987v3, Algorithm 1, PDF p.8. Each fresh copy undergoes the
frozen arbitrary-`t` amplitude-estimation routine: uniform `Fin t` control, controlled
powers of `U V`, inverse positive-sign QFT, and estimate `sin (pi j / t)^2`.
The product of the single-shot laws encodes independent executions. The fixed odd
repetition count is `2 * ceil (100 * log (1 / delta)) + 1`, and `realMedian` selects
the unique middle order statistic. No success or accuracy property is assumed here. -/
def monteCarloSuccessProb (S : CoherentValueSampler) (t : ℕ) (ht : 1 ≤ t)
    (delta radius : ℝ) : ℝ :=
  open Classical in
  ∑ z : Fin (boundedMeanRepetitions delta) → Fin t,
    if |realMedian (List.ofFn fun i => Real.sin (Real.pi * (z i : ℕ) / t) ^ 2) -
        samplerMean S| ≤ radius
    then ∏ i, boundedMeanShot S t ht (z i) else 0


end QAlgorithms.Papers.RoadmapA22


