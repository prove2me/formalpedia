-- Prove2me | Definitions.Def_GuoZhaoADRC_lyapV1
-- name    : GuoZhaoADRC_lyapV1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:46.409439+00:00
-- url     : https://prove2.me/theorems/0de64cb4-030b-4ee8-8be5-b3afbfdc46e3
-- title:
--   $V_1(e)=\sum_i V_1^i(e^i)$ (1.7)
-- statement:
--   For $e=(e^1,\dots,e^m)$ with $e^i\in\mathbb R^{n_i+1}$, $V_1(e)=\sum_{i=1}^mV_1^i(e^i)$, the Lyapunov function of the whole observer error built from the functions of Assumption A2.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (1.7), p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **`V_1(e) = ∑_{i=1}^m V_1^i(e^i)`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (1.7), p.1730. -/
noncomputable def lyapV1 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (e : (i : Fin m) → EuclideanSpace ℝ (Fin (n i + 1))) : ℝ :=
  ∑ i, D.V1 i (e i)

end GuoZhaoADRC


