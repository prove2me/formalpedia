-- Prove2me | Definitions.Def_GuoZhaoADRC_Pi1
-- name    : GuoZhaoADRC_Pi1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:53.820452+00:00
-- url     : https://prove2.me/theorems/06c879c9-9442-4c10-a7af-a00970f22f2d
-- title:
--   $\Pi_1=\min_i\lambda^i_{13}-\sum_i\beta^i_1\Xi^i$ (3.14)
-- statement:
--   $$\Pi_1=\min_{1\le i\le m}\lambda^i_{13}-\sum_{i=1}^m\beta^i_1\Xi^i.$$
--
--   Condition (3.1) of GA2 says exactly that $\Pi_1>0$. Then $\Pi_1/\varepsilon$ is the decay rate of the observer part of the Lyapunov function.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.14), p.1739

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_minOver
import Definitions.Def_GuoZhaoADRC_Xi

namespace GuoZhaoADRC

/-- **`Π₁ = min_i λ^i_13 − ∑_i β^i_1 Ξ^i`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.14), p.1739.

By (3.1) (corrected), `Π₁ > 0`. -/
noncomputable def Pi1 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) : ℝ :=
  minOver D.hm D.lam13 - ∑ i, D.beta1 i * Xi D i

end GuoZhaoADRC


