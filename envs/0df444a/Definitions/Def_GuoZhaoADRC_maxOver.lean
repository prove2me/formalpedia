-- Prove2me | Definitions.Def_GuoZhaoADRC_maxOver
-- name    : GuoZhaoADRC_maxOver
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:52.749474+00:00
-- url     : https://prove2.me/theorems/7c88eafa-2667-4117-a64e-5c5a0ce50ce9
-- title:
--   Maximum over the subsystems $\max_{1\le i\le m} v_i$
-- statement:
--   For $m\ge1$ and real numbers $v_1,\dots,v_m$, this is $\max_{1\le i\le m}v_i$, the quantity written $\max\{\lambda^i_{12}\}$ in (3.21)–(3.24).
--
--   **Formalization Note** It is `Finset.sup'` over the nonempty index set `Fin m`.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, notation max{λ^i_12} of (3.21)–(3.24), pp.1740–1741

import Mathlib

namespace GuoZhaoADRC

/-- **The maximum over the subsystems, `max_{1 ≤ i ≤ m} v_i`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), notation `max{λ^i_12}` of (3.21)–(3.24),
pp.1740–1741.

**Formalization Note.** `Finset.sup'` over the nonempty `Fin m` (`0 < m`). -/
noncomputable def maxOver {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ v

end GuoZhaoADRC


