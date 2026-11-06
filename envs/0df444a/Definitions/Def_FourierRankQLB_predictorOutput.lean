-- Prove2me | Definitions.Def_FourierRankQLB_predictorOutput
-- name    : FourierRankQLB_predictorOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:16.081047+00:00
-- url     : https://prove2.me/theorems/66ad6d4c-b651-43d3-9ff2-63c0004009cc
-- title:
--   Step (4) of the determinant predictor
-- statement:
--   From outputs $z_1,\dots,z_{125}$ with median $\hat Z$, the prediction
--   $$
--   \begin{cases}-1,&\hat Z>9/16,\\+1,&\text{otherwise.}\end{cases}
--   $$
--   The threshold $9/16$ separates the two components, by Lemma 4.7.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §4.4, step (4), p.29

import Mathlib
import Definitions.Def_FourierRankQLB_median125

namespace FourierRankQLB

/-- Step (4) of the predictor: output `-1` if the median exceeds `9/16`, and `+1` otherwise.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §4.4, step (4), p. 29. -/
noncomputable def predictorOutput (z : Fin 125 → ℝ) : ℝ := if 9 / 16 < median125 z then -1 else 1

end FourierRankQLB


