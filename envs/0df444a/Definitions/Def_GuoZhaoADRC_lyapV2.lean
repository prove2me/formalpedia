-- Prove2me | Definitions.Def_GuoZhaoADRC_lyapV2
-- name    : GuoZhaoADRC_lyapV2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:44.491594+00:00
-- url     : https://prove2.me/theorems/4a249bca-2674-4dbc-8331-76b9f47746e6
-- title:
--   $V_2(\eta)=\sum_i V_2^i(\eta^i)$ (1.7)
-- statement:
--   For $\eta=(\eta^1,\dots,\eta^m)$ with $\eta^i\in\mathbb R^{n_i}$, $V_2(\eta)=\sum_{i=1}^mV_2^i(\eta^i)$, the Lyapunov function of the whole tracking error built from the functions of Assumption A3.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (1.7), p.1730

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **`V_2(η) = ∑_{i=1}^m V_2^i(η^i)`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (1.7), p.1730. -/
noncomputable def lyapV2 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (η : (i : Fin m) → EuclideanSpace ℝ (Fin (n i))) : ℝ :=
  ∑ i, D.V2 i (η i)

end GuoZhaoADRC


