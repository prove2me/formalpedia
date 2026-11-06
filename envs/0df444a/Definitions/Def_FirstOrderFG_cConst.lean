-- Prove2me | Definitions.Def_FirstOrderFG_cConst
-- name    : FirstOrderFG_cConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:26.207685+00:00
-- url     : https://prove2.me/theorems/25981bf2-9ad0-441c-92f4-b1f40ffa66ab
-- title:
--   The universal constant $c=1/(2^{13}e^2)$
-- statement:
--   The universal constant of Theorem 4.2 and Algorithm 4 is
--   $$
--   c=\frac1{2^{13}e^2}.
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Theorem 4.2, p.31; App. B, p.21; Algorithm 4, lines 1, 7, p.32

import Mathlib

namespace FirstOrderFG

/-- **The universal constant `c = 1/(2¹³e²)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Theorem 4.2, p.31 ("Choose
`c = 1/(2^13 e^2)`"); App. B, p.21: "Throughout, `c > 0` is the universal constant in Theorem 4.2";
it is the constant of Algorithm 4, lines 1 and 7, p.32. -/
noncomputable def cConst : ℝ :=
  1 / (2 ^ 13 * Real.exp 2)

end FirstOrderFG


