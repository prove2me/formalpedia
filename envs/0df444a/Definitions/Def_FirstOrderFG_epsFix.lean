-- Prove2me | Definitions.Def_FirstOrderFG_epsFix
-- name    : FirstOrderFG_epsFix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:29.34442+00:00
-- url     : https://prove2.me/theorems/cf3e48af-8556-4ccf-b909-8f9ce9b956dd
-- title:
--   Fixed-point accuracy $\varepsilon=1/(KT^2)$
-- statement:
--   Algorithm 2 computes an $\varepsilon$-fixed point with
--   $$
--   \varepsilon=\frac{1}{KT^2}.
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 1, p.10

import Mathlib

namespace FirstOrderFG

/-- **The fixed-point accuracy `ε = 1/(KT²)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 1, p.10. -/
noncomputable def epsFix (K T : ℕ) : ℝ :=
  1 / ((K : ℝ) * (T : ℝ) ^ 2)

end FirstOrderFG


