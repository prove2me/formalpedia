-- Prove2me | Definitions.Def_CongestionTaxes_IsSolution
-- name    : CongestionTaxes_IsSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:35.591683+00:00
-- url     : https://prove2.me/theorems/7b8349df-b3bf-4af6-9c56-3886d8f0c6be
-- title:
--   Solution of the convex program (12)
-- statement:
--   A point $\bigl((\bar y_i)_i,(\bar v_r)_r\bigr)$ is a **solution of program (12)** if it is feasible and its objective $\sum_r p_r(\bar v_r)$ is at most the objective of every feasible point. The parameter vector of the optimal taxes of Theorem 3 is $(\bar v_r)_r$.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (12) and Theorem 3, p.19

import Mathlib
import Definitions.Def_CongestionTaxes_IsFeasible
import Definitions.Def_CongestionTaxes_objective

namespace CongestionTaxes

/-- `((y_i), (v_r))` is a **solution of the convex program (12)** (Paccagnan, Gairing,
arXiv:2105.07480v2, (12) and Theorem 3, p.19): it is feasible and its objective `∑_r p_r(v_r)` is
at most that of every feasible point. -/
def IsSolution {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (y : ι → Finset E → ℝ) (v : E → ℝ) : Prop :=
  IsFeasible G y v ∧ ∀ y' v', IsFeasible G y' v' → objective G v ≤ objective G v'

end CongestionTaxes


