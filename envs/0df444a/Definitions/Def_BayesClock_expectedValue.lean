-- Prove2me | Definitions.Def_BayesClock_expectedValue
-- name    : BayesClock_expectedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:25.079278+00:00
-- url     : https://prove2.me/theorems/d66cc470-d776-4512-9055-feb6862095c1
-- title:
--   Expected value $\mathbb E[v_i]$
-- statement:
--   $\mathbb E[v_i]=\int x\,\mathrm dD_i(x)$ is the expected value of bidder $i$.
--
--   **Formalization Note** A lower integral, which may equal $\infty$.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, p.9

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- `E[vᵢ]` for a value with law `ν₀`, the mean used on p.9 of Feldman et al.,
arXiv:2202.09291v1.

**Formalization Note** A lower Lebesgue integral with values in `ℝ≥0∞`; the mean may be `∞`. -/
noncomputable def expectedValue (ν₀ : Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ∂ν₀

end BayesClock


