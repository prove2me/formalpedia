-- Prove2me | Definitions.Def_FirstOrderFG_Fmap
-- name    : FirstOrderFG_Fmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:49.189676+00:00
-- url     : https://prove2.me/theorems/f969d7ec-b5ee-42bb-a1b5-40167e2c37f7
-- title:
--   The smoothed fixed-point map $F_{p,\gamma}$
-- statement:
--   For a distribution $p$ on $V_{\mathrm{self}}$ and $\gamma>0$, the map $F_{p,\gamma}$ on distributions over $V_{\mathrm{self}}$ is
--   $$
--   [F_{p,\gamma}(q)]_i=\frac{p_i\,\psi_\gamma\big(Q_i^{G_{\mathrm{self}}}(q)\big)}{\sum_{j\in V_{\mathrm{self}}}p_j\,\psi_\gamma\big(Q_j^{G_{\mathrm{self}}}(q)\big)},\qquad i\in V_{\mathrm{self}} .
--   $$
--   The base learner samples from an approximate fixed point of $F_{p_t,\eta_t/x_{t,0}}$.
--
--   **Formalization Note** The map returns $0$ on coordinates outside $V_{\mathrm{self}}$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Proposition A.3, p.20; Eq. (22), p.9

import Mathlib
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Qself
import Definitions.Def_FirstOrderFG_psi

namespace FirstOrderFG

/-- **The smoothed fixed-point map `F_{p,γ}`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Proposition A.3, p.20:
`[F_{p,γ}(q)]_i ≜ p_i ψ_γ(Q_i^{G_self}(q)) / ∑_{j ∈ V_self} p_j ψ_γ(Q_j^{G_self}(q))` for
`i ∈ V_self`; Eq. (22), p.9, is `F_t^{self} = F_{p_t, η_t/x_{t,0}}`.

**Formalization Note.** Distributions on `V_self` are functions `Fin K → ℝ`; the map returns `0`
on the coordinates outside `V_self`. -/
noncomputable def Fmap {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (p : Fin K → ℝ) (γ : ℝ) (q : Fin K → ℝ) : Fin K → ℝ :=
  fun i => if i ∈ Vself E then
    p i * psi K T γ (Qself E q i) / ∑ j ∈ Vself E, p j * psi K T γ (Qself E q j)
  else 0

end FirstOrderFG


