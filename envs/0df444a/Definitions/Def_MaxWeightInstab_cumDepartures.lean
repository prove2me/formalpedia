-- Prove2me | Definitions.Def_MaxWeightInstab_cumDepartures
-- name    : MaxWeightInstab_cumDepartures
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:52.850288+00:00
-- url     : https://prove2.me/theorems/f03b5e9d-02ac-469e-a952-97f1fefda446
-- title:
--   Cumulative departures $D_j(t)$
-- statement:
--   Along a trajectory, $D_j(t)$ is the number of jobs served at queue $j$ in time units $1,\dots,t$; $D_j(0)=0$.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, (7c)–(8), p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_Trajectory
import Definitions.Def_MaxWeightInstab_departure

namespace MaxWeightInstab

/-- `D_q(t)`, the cumulative number of departures from queue `q` by time `t` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, (7c)–(8), p.5),
along a trajectory: the jobs served at `q` in time units `1, …, t`. `D_q(0) = 0`. -/
def cumDepartures {J ν : ℕ} (tr : Trajectory J ν) (q : Queue J) (t : ℕ) : ℕ :=
  ∑ τ ∈ Finset.range t, departure (tr.Q τ) (tr.σ (τ + 1)) q

end MaxWeightInstab


