-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_qOf
-- name    : FirstOrderFG_Alg2_qOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:50:31.109526+00:00
-- url     : https://prove2.me/theorems/3c767e50-4990-48f5-aaa5-fb919c6e465c
-- title:
--   Base sampling distribution $q_t$ (line 6)
-- statement:
--   At round $t$ the base learner samples from $q_t$, the interior $\varepsilon$-fixed point of $F_{p_t,\gamma}$ with $\gamma=\eta_t/x_{t,0}$ and $\varepsilon=1/(KT^2)$, computed by Picard iteration from the start $q_0(p_t,\gamma)$ given by an admissible start rule.
--
--   **Formalization Note** When $V_{\mathrm{self}}=\emptyset$ the base learner does not run and $q_t$ is set to $0$ (never read).
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 6, p.10; Eq. (22), p.9

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_State
import Definitions.Def_FirstOrderFG_Alg2_eta
import Definitions.Def_FirstOrderFG_picardFixed

namespace FirstOrderFG

/-- **The base sampling distribution `q_t` (Algorithm 2, line 6).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 6,
p.10, and Eq. (22), p.9: `q_t` is the interior `ε`-fixed point of
`q ↦ (p_{t,i} ψ_t(Q_i^{G_self}(q)) / ∑_{j} p_{t,j} ψ_t(Q_j^{G_self}(q)))_{i ∈ V_self}`, with
`ψ_t(v) = (v + 1/(KT))/(v + η_t/x_{t,0})`, computed by Picard iteration.

**Formalization Note.** The Picard iteration starts at `q₀ p γ` for the admissible start rule `q₀`
(`InteriorStart`) with `γ = η_t/x_{t,0}`. When `V_self` is empty the base learner does not run and
`q_t` is set to `0` (never read). -/
noncomputable def Alg2.qOf {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ)
    (st : Alg2.State K) : Fin K → ℝ :=
  if (Vself E).Nonempty then
    picardFixed E T st.p (Alg2.eta E T st / st.x none) (q₀ st.p (Alg2.eta E T st / st.x none))
  else 0

end FirstOrderFG


