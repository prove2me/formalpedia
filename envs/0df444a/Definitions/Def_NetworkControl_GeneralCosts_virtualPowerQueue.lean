-- Prove2me | Definitions.Def_NetworkControl_GeneralCosts_virtualPowerQueue
-- name    : NetworkControl_GeneralCosts_virtualPowerQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:24:55.867538+00:00
-- url     : https://prove2.me/theorems/9386726e-1505-49e9-b874-86c05041ea34
-- title:
--   Virtual power queue recursion, Eq. (6.13), p. 114
-- statement:
--   The virtual power queue recursion, Eq. (6.13), p. 114: $D(t{+}1)=\max[D(t)-P_{av},0]
--   +\sum_i P_i(t)$, with initial condition $D(0)=0$. $P:\mathbb N\to\mathrm{Fin}\,L\to\mathbb R$
--   is the power-allocation process.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 114, Eq. (6.13)

import Mathlib

namespace NetworkControl.GeneralCosts

/-- The virtual power queue recursion, Eq. (6.13), p. 114: `D(t+1) = max[D(t)-Pav,0] + Σ_i P_i(t)`,
with initial condition `D(0) = 0`. `P : ℕ → Fin L → ℝ` is the power-allocation process. -/
def virtualPowerQueue {L : ℕ} (P : ℕ → Fin L → ℝ) (Pav : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => max (virtualPowerQueue P Pav t - Pav) 0 + ∑ i : Fin L, P t i

end NetworkControl.GeneralCosts


