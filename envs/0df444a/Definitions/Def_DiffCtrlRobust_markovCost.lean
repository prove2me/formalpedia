-- Prove2me | Definitions.Def_DiffCtrlRobust_markovCost
-- name    : DiffCtrlRobust_markovCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:22.075114+00:00
-- url     : https://prove2.me/theorems/f0258fea-6588-465c-a19a-f558b83b90f6
-- title:
--   The cost $\mathcal J^{v}_\alpha(x,c)$ of a stationary Markov control
-- statement:
--   For $v\in\mathfrak U_{\mathsf{sm}}$ and a state process $X$, the cost is
--
--   $$
--   \mathcal J^{v}_\alpha(x,c)=\mathbb E^{v}_x\left[\int_0^\infty e^{-\alpha s}c(X_s,v(X_s))\,\mathrm ds\right],
--   $$
--
--   the discounted cost of the control $U_t=v(X_t)$. Equation (3.17) is this cost with $v=v^*_n$ and $X=\hat X^n$, the solution of the true dynamics (2.1) under the policy $v^*_n$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, p.13, (3.17)

import Definitions.Def_DiffCtrlRobust_discCost
import Definitions.Def_DiffCtrlRobust_Usm

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The cost (3.17) of a stationary Markov control `v` along a state process `X`
(arXiv:2205.05894v2, p.13): `𝔼[∫₀^∞ e^{-α s} c(X_s, v(X_s)) ds]`, the discounted cost of the
control `u_t = v(X_t)`. -/
noncomputable def markovCost {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*}
    [MeasurableSpace U] (P : Measure Ω) (α : ℝ) (c : SDEState d → U → ℝ) (v : Usm d U)
    (X : ℝ≥0 → Ω → SDEState d) : ℝ :=
  discCost P α c (fun t ω => v.1 (X t ω)) X

end DiffCtrlRobust


