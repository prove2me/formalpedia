-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_alphaBound
-- name    : FirstOrderFG_Supplement_alphaBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:46:39.137578+00:00
-- url     : https://prove2.me/theorems/adf81a1e-f9db-4d87-87f8-b386fc9cf2be
-- title:
--   Explicit independence-number bound on $H^G$
-- statement:
--   The explicit graph bound from Lemma 2.1 is
--
--   $$
--   A_G=2\alpha\ln\!\left(1+\frac{K^3T+K}{\alpha}\right)+2.
--   $$
--
--   It is the concrete value substituted into the optimized clauses of the supplement.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma 2.1, p.4

import Mathlib
import Definitions.Def_FirstOrderFG_indepNumber

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The explicit Lemma 2.1 graph bound used by the supplement.**
Zhang–Zhang–Luo–Mineiro, arXiv:2610.40861, Lemma 2.1, p.4:
`2α ln(1 + (K³T+K)/α) + 2`. -/
noncomputable def alphaBound {K : ℕ} (E : Fin K → Fin K → Prop) (T : ℕ) : ℝ :=
  2 * (FirstOrderFG.indepNumber E : ℝ) *
      Real.log (1 + ((K : ℝ) ^ 3 * T + K) / FirstOrderFG.indepNumber E) + 2

end FirstOrderFG.Supplement


