-- Prove2me | Definitions.Def_GuoZhaoADRC_minOver
-- name    : GuoZhaoADRC_minOver
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:43.508532+00:00
-- url     : https://prove2.me/theorems/5a05c1c1-7ea9-4097-bedb-e880746eee1d
-- title:
--   Minimum over the subsystems $\min_{1\le i\le m} v_i$
-- statement:
--   For $m\ge1$ and real numbers $v_1,\dots,v_m$, this is $\min_{1\le i\le m}v_i$, the quantity written $\min\{\lambda^i_{13}\}$, $\min\{\lambda^i_{23}\}$, $\min\{\lambda^i_{11}\}$ and so on in (3.1) and (3.14)–(3.29).
--
--   **Formalization Note** It is `Finset.inf'` over the nonempty index set `Fin m`, so it is the true minimum, with no default value.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, notation min{λ^i_13} of (3.1), (3.14), (3.21)–(3.29), pp.1737–1741

import Mathlib

namespace GuoZhaoADRC

/-- **The minimum over the subsystems, `min_{1 ≤ i ≤ m} v_i`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), notation `min{λ^i_13}` etc. of (3.1), (3.14),
(3.21)–(3.29), pp.1737–1741.

**Formalization Note.** `Finset.inf'` over the nonempty `Fin m` (`0 < m`); this is the true
minimum, with no default value. -/
noncomputable def minOver {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ v

end GuoZhaoADRC


