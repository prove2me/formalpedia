-- Prove2me | Definitions.Def_CongestionTaxes_objective
-- name    : CongestionTaxes_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:44.960493+00:00
-- url     : https://prove2.me/theorems/1e866c70-13cd-4b9f-8f13-35c2aa66251d
-- title:
--   Objective $\sum_r p_r(v_r)$ of program (12)
-- statement:
--   The objective of the convex program (12) at the load vector $(v_r)_r$ is
--
--   $$
--   \sum_{r\in\mathcal R}p_r(v_r),
--   $$
--
--   where $p_r$ is the Poisson expected cost (10) of the resource cost $\ell_r$. It is the continuous relaxation of $\mathrm{MinSC}$ in which each $c_r(x)=x\ell_r(x)$ is replaced by $p_r$.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, display (12), p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_poissonValue

namespace CongestionTaxes

/-- The **objective of the convex program (12)** (Paccagnan, Gairing, arXiv:2105.07480v2, (12),
p.19): `∑_{r ∈ 𝓡} p_r(v_r)`, with `p_r` the Poisson expected cost (10) of the resource cost `ℓ_r`. -/
noncomputable def objective {ι E : Type*} [Fintype E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E) (v : E → ℝ) : ℝ :=
  ∑ r, poissonValue (G.latency r) (v r)

end CongestionTaxes


