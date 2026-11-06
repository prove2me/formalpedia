-- Prove2me | Definitions.Def_FirstOrderFG_GammaA
-- name    : FirstOrderFG_GammaA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:36.637344+00:00
-- url     : https://prove2.me/theorems/9061ea04-d4d5-47f9-ae41-6f3ad9469be6
-- title:
--   $\Gamma_A=AJ\ln(KT)$
-- statement:
--   For a bound $A$,
--   $$
--   \Gamma_A=A\,J\,\ln(KT),
--   $$
--   with $J=\lceil\log_2(2MT)\rceil$ and the natural logarithm. Algorithm 4 sets the master rate to $c/\Gamma_A$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §4.2, p.11

import Mathlib
import Definitions.Def_FirstOrderFG_Jconst

namespace FirstOrderFG

/-- **`Γ_A = A·J·ln(KT)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §4.2, p.11 ("Denote by `Γ_A ≜ AJ ln(KT)`").

**Formalization Note.** `ln` is the natural logarithm `Real.log`; `K` is the number of arms. -/
noncomputable def GammaA {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (A : ℝ) : ℝ :=
  A * (Jconst E T : ℝ) * Real.log ((K : ℝ) * T)

end FirstOrderFG


