-- Prove2me | Definitions.Def_MaxWeightInstab_totalA
-- name    : MaxWeightInstab_totalA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:27.741345+00:00
-- url     : https://prove2.me/theorems/f0255c43-58ff-42ab-b952-e606c6e7cead
-- title:
--   Total queue length $Q^\Sigma_{\mathcal A}$ of component $\mathcal A$
-- statement:
--   $Q^\Sigma_{\mathcal A}=\sum_{j=0}^J Q_{\mathcal A_j}$, the number of jobs at component $\mathcal A$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_State

namespace MaxWeightInstab

/-- `Q^Σ_𝒜 = ∑_{j=0}^J Q_{𝒜_j}`, the number of jobs at component `𝒜` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.5). -/
def totalA {J : ℕ} (x : State J) : ℕ :=
  ∑ i : Fin (J + 1), x (Sum.inl i)

end MaxWeightInstab


