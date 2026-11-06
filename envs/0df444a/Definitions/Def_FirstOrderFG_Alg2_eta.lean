-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_eta
-- name    : FirstOrderFG_Alg2_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:43.576419+00:00
-- url     : https://prove2.me/theorems/c655b004-1c78-46f1-a1e8-5f672bada19e
-- title:
--   Adaptive base learning rate $\eta_t$ (Eq. (24))
-- statement:
--   The base learning rate at round $t$ is
--   $$
--   \eta_t=\sqrt{\frac{\ln(sT)}{2A\big(1+\sum_{\tau=1}^{t-1}\tilde g_{\tau,0}/x_{\tau,0}\big)}},
--   $$
--   the sum running over the instance's earlier rounds.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (24), p.9; Algorithm 2, line 5, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_State
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The adaptive base learning rate `η_t` (Eq. (24)).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (24), p.9, and Algorithm 2,
line 5, p.10: `η_t = √( ln(sT) / (2A(1 + ∑_{τ=1}^{t−1} g̃_{τ,0}/x_{τ,0})) )`, the sum running over this
instance's earlier rounds.

**Formalization Note.** `ln` is `Real.log`; it is used only when `s = |V_self| > 0`. -/
noncomputable def Alg2.eta {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (st : Alg2.State K) : ℝ :=
  Real.sqrt (Real.log (((Vself E).card : ℝ) * T) / (2 * st.A * (1 + st.gsum)))

end FirstOrderFG


