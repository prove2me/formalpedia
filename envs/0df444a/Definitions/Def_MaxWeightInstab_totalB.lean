-- Prove2me | Definitions.Def_MaxWeightInstab_totalB
-- name    : MaxWeightInstab_totalB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:39.131023+00:00
-- url     : https://prove2.me/theorems/7d0d0616-8d55-4256-abff-17477a4cc97b
-- title:
--   Total queue length $Q^\Sigma_{\mathcal B}$ of component $\mathcal B$
-- statement:
--   $Q^\Sigma_{\mathcal B}=\sum_{j=0}^J Q_{\mathcal B_j}$, the number of jobs at component $\mathcal B$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_State

namespace MaxWeightInstab

/-- `Q^Σ_ℬ = ∑_{j=0}^J Q_{ℬ_j}`, the number of jobs at component `ℬ` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.5). -/
def totalB {J : ℕ} (x : State J) : ℕ :=
  ∑ i : Fin (J + 1), x (Sum.inr i)

end MaxWeightInstab


