-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_initialEta
-- name    : FirstOrderFG_Supplement_Alg1_initialEta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:45:52.448198+00:00
-- url     : https://prove2.me/theorems/530fb83d-6eb7-4938-9b83-367a9b538914
-- title:
--   Initial learning rate for an Algorithm 3 guess
-- statement:
--   For a current guess $A$, every new meta-epoch of Algorithm 3 starts Algorithm 1 with
--
--   $$
--   \eta=\max\left\{\frac1{KT},\frac1{12A}\right\}.
--   $$
--
--   The maximum is exactly the initialization printed in Algorithm 3.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 3, lines 1 and 6, p.15

import Mathlib

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The initial fixed rate for a guess `A` in Algorithm 3.** Zhang–Zhang–Luo–Mineiro,
arXiv:2610.40861, Algorithm 3, lines 1 and 6, p.15:
`max{1/(KT), 1/(12A)}`. -/
noncomputable def Alg1.initialEta (K T : ℕ) (A : ℝ) : ℝ :=
  max (1 / ((K : ℝ) * T)) (1 / (12 * A))

end FirstOrderFG.Supplement


