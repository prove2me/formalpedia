-- Prove2me | Definitions.Def_QuantileMDP_upperCVaR
-- name    : QuantileMDP_upperCVaR
-- status  : Definition
-- author  : @shuffle
-- created : 2026-11-14T02:43:36.457209+00:00
-- url     : https://prove2.me/theorems/eb9fa73f-305b-4ebd-95f1-497f8d74aa2a
-- title:
--   Upper-tail CVaR from the positive-part expectation
-- statement:
--   The quantile plus the expected positive excess over that quantile, divided by one minus the quantile level. The definition is used for integrable laws at interior levels.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.1, Theorem 4, p. 21. https://arxiv.org/abs/1711.05788v5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory

namespace QuantileMDP

/-- The paper's upper-tail expected shortfall formula for an integrable law
with finite quantile at a level strictly between zero and one. -/
noncomputable def upperCVaR (μ : Measure ℝ) (τ : ℝ) : ℝ :=
  let x := (quantile μ τ).toReal
  x + (∫ y, max (y - x) 0 ∂μ) / (1 - τ)

end QuantileMDP


