-- Prove2me | Definitions.Def_ParetoIneff_costMatrix
-- name    : ParetoIneff_costMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:57.094773+00:00
-- url     : https://prove2.me/theorems/5b8cd640-0fc3-4ae1-8e36-9c3ddff19b37
-- title:
--   A profile as a real cost matrix
-- statement:
--   A true profile $t\in\mathbb R_{\ge0}^{n\times m}$, viewed as the real $n\times m$ matrix with entries $t_{i,j}$.
--
--   This is the data of the published load and makespan of unrelated-machine scheduling (`MatousekLP.Scheduling`), which this mission reuses instead of redefining.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib

open NNReal

namespace ParetoIneff

/-- A true profile `t ∈ ℝ≥0^{n×m}`, arXiv:1809.03454v7, p.5, as a real `n × m` matrix, the form in
which the published load and makespan of `MatousekLP.Scheduling` take their data. -/
def costMatrix {n m : ℕ} (t : Fin n → Fin m → ℝ≥0) : Matrix (Fin n) (Fin m) ℝ :=
  fun i j => (t i j : ℝ)

end ParetoIneff


