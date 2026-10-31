-- Prove2me | Definitions.Def_GuoZhaoADRC_lamMin
-- name    : GuoZhaoADRC_lamMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:59.792991+00:00
-- url     : https://prove2.me/theorems/d864eb5c-f6e5-43a7-9388-1d89e54a6f69
-- title:
--   $\lambda=\min_i\lambda^i_{23}$ (3.14)
-- statement:
--   $\lambda=\min_{1\le i\le m}\lambda^i_{23}$, the decay rate of the tracking part of the Lyapunov function.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.14), p.1739

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_minOver

namespace GuoZhaoADRC

/-- **`λ = min_i λ^i_23`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.14), p.1739. -/
noncomputable def lamMin {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) : ℝ :=
  minOver D.hm D.lam23

end GuoZhaoADRC


