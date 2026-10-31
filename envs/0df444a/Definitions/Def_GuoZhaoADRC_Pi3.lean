-- Prove2me | Definitions.Def_GuoZhaoADRC_Pi3
-- name    : GuoZhaoADRC_Pi3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:09.985586+00:00
-- url     : https://prove2.me/theorems/7f76e6f4-ed07-429a-b542-7256687b6fe3
-- title:
--   $\Pi_3=\sum_i\beta^i_1\Xi^i_0$ (3.14)
-- statement:
--   For constants $\Xi^1_0,\dots,\Xi^m_0$ (those of (3.9)), $\Pi_3=\sum_{i=1}^m\beta^i_1\Xi^i_0$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.14), p.1739

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **`Π₃ = ∑_i β^i_1 Ξ^i_0`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.14), p.1739.

**Formalization Note.** The constants `Ξ^i_0` of (3.9) are an argument. -/
noncomputable def Pi3 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (Ξ₀ : Fin m → ℝ) : ℝ :=
  ∑ i, D.beta1 i * Ξ₀ i

end GuoZhaoADRC


