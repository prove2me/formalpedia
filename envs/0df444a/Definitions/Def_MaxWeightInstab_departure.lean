-- Prove2me | Definitions.Def_MaxWeightInstab_departure
-- name    : MaxWeightInstab_departure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:13:33.378094+00:00
-- url     : https://prove2.me/theorems/ef0c568e-ca52-44ad-a2bb-d340a3a96452
-- title:
--   Jobs served at a queue in one time unit
-- statement:
--   With queue lengths $Q$ and schedule $\sigma$, queue $j$ completes $\sigma_j\wedge Q_j$ jobs in the time unit: jobs are unit sized, so every unit of service at a nonempty queue completes one job (the summand of the cumulative service (8)).
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (8), p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_State

namespace MaxWeightInstab

/-- The number of jobs served at queue `q` in one time unit when the queue lengths are `x` and the
schedule is `σ`: `π_j(Q) ∧ Q_j`, the summand of the cumulative service (8) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.5). Jobs are
unit sized (`p_j = 1`), so every unit of service at a nonempty queue completes one job. -/
def departure {J : ℕ} (x σ : State J) (q : Queue J) : ℕ :=
  min (σ q) (x q)

end MaxWeightInstab


