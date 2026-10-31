-- Prove2me | Definitions.Def_GuoZhaoADRC_ctrl
-- name    : GuoZhaoADRC_ctrl
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:48.665115+00:00
-- url     : https://prove2.me/theorems/03214706-cded-4cdb-a12c-262635b1a5f6
-- title:
--   The control $u_k=\sum_l b^*_{kl}u^*_l$ of ADRC(G) (3.2)
-- statement:
--   The control actually applied to the plant is
--
--   $$u_k(t)=\sum_{l=1}^m b^*_{kl}\,u^*_l(t),$$
--
--   where $(b^*_{kl})$ is the inverse of the nominal gain matrix $(b_{ik})$ of GA2 and $u^*_l$ is the virtual control of (3.2).
--
--   **Formalization Note** $(b^*_{kl})$ is the matrix inverse `b⁻¹`, which is the true inverse because `ADRCHyp` assumes $(b_{ik})$ invertible.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.2) and GA2, pp.1736–1737

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData
import Definitions.Def_GuoZhaoADRC_uStar

namespace GuoZhaoADRC

/-- **The control `u_k = ∑_l b*_kl u*_l` of ADRC(G) (3.2).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.2) and GA2, pp.1736–1737.

**Formalization Note.** `(b*_kl)` is the matrix inverse `b⁻¹` (GA2); `ADRCHyp` assumes `b`
invertible, so this is the true inverse. -/
noncomputable def ctrl {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (xhat : ℝ → (i : Fin m) → Fin (n i + 1) → ℝ) (k : Fin m) (t : ℝ) : ℝ :=
  ∑ l, D.b⁻¹ k l * uStar D xhat l t

end GuoZhaoADRC


