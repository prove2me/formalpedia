-- Prove2me | Definitions.Def_CongestionTaxes_IsApproxSolution
-- name    : CongestionTaxes_IsApproxSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:43.114489+00:00
-- url     : https://prove2.me/theorems/f3738ec8-33e1-48b0-9951-cdb0db8f3d4a
-- title:
--   $(1+\xi)$-approximate solution of program (12)
-- statement:
--   For $\xi\ge0$, a point $\bigl((y_i)_i,(v_r)_r\bigr)$ is a **$(1+\xi)$-approximate solution of (12)** if it is feasible and
--
--   $$
--   \sum_r p_r(v_r)\le(1+\xi)\sum_r p_r(v'_r)\qquad\text{for every feasible }\bigl((y'_i)_i,(v'_r)_r\bigr).
--   $$
--
--   This is the precision at which the proof of Theorem 3 (p.20) solves (12): the fifth line of (14) then pays a factor $1+\xi$.
--
--   **Formalization Note** The point is exactly feasible and only the objective carries the error. For $\xi=0$ this is a solution of (12).
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, proof of Theorem 3, p.20

import Mathlib
import Definitions.Def_CongestionTaxes_IsFeasible
import Definitions.Def_CongestionTaxes_objective

namespace CongestionTaxes

/-- `((y_i), (v_r))` is a **`(1 + ξ)`-approximate solution of (12)** (Paccagnan, Gairing,
arXiv:2105.07480v2, proof of Theorem 3, second claim, p.20: (12) "can be solved to arbitrary
precision", and the fifth line of (14) then pays "a multiplicative factor 1 + ξ"): it is feasible
and its objective is at most `1 + ξ` times the objective of every feasible point.

**Formalization Note** The point stays exactly feasible; only the objective carries the error, as
on p.20. Comparing with every feasible point rather than with a real infimum avoids the junk value
of `⨅`; since the objective is nonnegative on feasible points, the two agree. At `ξ = 0` this is
`IsSolution`. -/
def IsApproxSolution {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq E] (ξ : ℝ)
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (y : ι → Finset E → ℝ) (v : E → ℝ) : Prop :=
  IsFeasible G y v ∧ ∀ y' v', IsFeasible G y' v' → objective G v ≤ (1 + ξ) * objective G v'

end CongestionTaxes


