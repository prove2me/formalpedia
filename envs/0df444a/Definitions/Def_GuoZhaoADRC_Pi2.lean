-- Prove2me | Definitions.Def_GuoZhaoADRC_Pi2
-- name    : GuoZhaoADRC_Pi2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:18.384695+00:00
-- url     : https://prove2.me/theorems/d2b7b8ab-36ba-48e9-9009-28241922227f
-- title:
--   $\Pi_2=\sum_i\beta^i_1\Xi^i_1$ (3.14)
-- statement:
--   For constants $\Xi^1_1,\dots,\Xi^m_1$ (those of (3.9)), $\Pi_2=\sum_{i=1}^m\beta^i_1\Xi^i_1$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.14), p.1739

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **`Π₂ = ∑_i β^i_1 Ξ^i_1`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.14), p.1739.

**Formalization Note.** The constants `Ξ^i_1` of (3.9) are an argument. -/
noncomputable def Pi2 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (Ξ₁ : Fin m → ℝ) : ℝ :=
  ∑ i, D.beta1 i * Ξ₁ i

end GuoZhaoADRC


