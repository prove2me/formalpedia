-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_batchRate
-- name    : ProcessingNetworks_MArP_batchRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:04.996554+00:00
-- url     : https://prove2.me/theorems/6ba3e86c-d712-498e-bcc6-91186b60bb46
-- title:
--   The long-run batch rate $\theta_k$ (eq. (E.6))
-- statement:
--   For a distribution $\pi$ on $\mathcal S$ and a batch type $k$,
--   $$
--   \theta_k=\sum_{s\in\mathcal S}\pi(s)\beta_k(s)+\sum_{s,\tilde s\in\mathcal S}\pi(s)\Lambda_{s\tilde s}\,q_k(s,\tilde s).
--   $$
--   When $\pi$ is the stationary distribution of the ARMC, this is the long-run rate of type-$k$ batches: spontaneous arrivals at rate $\beta_k(s)$ while in state $s$, and triggered arrivals at each transition.
--
--   **Formalization Note** The page prints $q(s,\tilde s)$ without a subscript in (E.6). The subscript $k$ is restored, since $\theta_k$ counts type-$k$ batches and the proof's (E.11)–(E.12) use $q_k$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), eq. (E.6), p.307 (PDF p.323)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_MArPData

namespace ProcessingNetworks.MArP

/-- The long-run rate of batches of type `k`, eq. (E.6) (Dai & Harrison, Processing Networks,
pre-publication draft 2020-4-2, p.307, PDF p.323):
`θ_k = ∑_{s} π(s) β_k(s) + ∑_{s, s̃} π(s) Λ_{s s̃} q_k(s, s̃)`.

**Formalization Note.** The page prints `q(s, s̃)` without the subscript `k`. The subscript is
restored: `θ_k` counts type-`k` batches, and the proof's (E.11)–(E.12) use `q_k`. The diagonal terms
vanish because `q_k(s, s) = 0`. -/
noncomputable def batchRate {I d r : ℕ} (D : MArPData I d r) (π : PMF (Fin d)) (k : Fin r) : ℝ :=
  ∑ s, (π s).toReal * D.β k s + ∑ s, ∑ s', (π s).toReal * D.Λ s s' * D.q k s s'

end ProcessingNetworks.MArP


