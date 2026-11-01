-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_arrivalRate
-- name    : ProcessingNetworks_MArP_arrivalRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:18.570667+00:00
-- url     : https://prove2.me/theorems/774c4967-c3c3-405d-abcd-a3e13495e53e
-- title:
--   The long-run arrival rate vector $\lambda$ (eq. (E.5))
-- statement:
--   The long-run arrival rate vector of a MArP is
--   $$
--   \lambda=\sum_{k=1}^r\delta^k\theta_k\in\mathbb R_+^I .
--   $$
--   Its $i$-th component is $\sum_k\delta^k_i\theta_k$, the sum of the batch rates weighted by the number of class $i$ arrivals in each batch.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), eq. (E.5), p.307 (PDF p.323)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_batchRate

namespace ProcessingNetworks.MArP

/-- The long-run arrival rate vector `λ = ∑_{k=1}^r δᵏ θ_k`, eq. (E.5) (Dai & Harrison, Processing
Networks, pre-publication draft 2020-4-2, p.307, PDF p.323). -/
noncomputable def arrivalRate {I d r : ℕ} (D : MArPData I d r) (π : PMF (Fin d)) (i : Fin I) : ℝ :=
  ∑ k, (D.δ k i : ℝ) * batchRate D π k

end ProcessingNetworks.MArP


