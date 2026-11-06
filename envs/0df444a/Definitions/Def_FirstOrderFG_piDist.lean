-- Prove2me | Definitions.Def_FirstOrderFG_piDist
-- name    : FirstOrderFG_piDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:43.631065+00:00
-- url     : https://prove2.me/theorems/3c7809d4-fa52-4fcc-b316-73588e0a6cfe
-- title:
--   The played distribution $\pi_t$ (Eq. (18))
-- statement:
--   Given the master distribution $x\in\Delta(\mathcal B)$ and the base distribution $q\in\Delta(V_{\mathrm{self}})$, the played arm $I_t$ has law
--   $$
--   \pi_i=\begin{cases}x_0\,q_i,& i\in V_{\mathrm{self}},\\ x_i,& i\in\bar V_{\mathrm{self}}.\end{cases}
--   $$
--   The master draws $B_t\sim x$; if $B_t=0$ the base learner draws $I_t\sim q$, otherwise $I_t=B_t$.
--
--   **Formalization Note** $B_t$ is a function of $I_t$ ($B_t=0$ iff $I_t\in V_{\mathrm{self}}$), so the whole randomness of a round is $I_t$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (18), p.8; Algorithm 2, lines 7–9, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The played distribution `π_t` (Eq. (18)).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (18), p.8, and Algorithm 2, line 7:
`π_{t,i} = x_{t,0} q_{t,i}` for `i ∈ V_self` and `π_{t,i} = x_{t,i}` for `i ∈ V̄_self`.

**Formalization Note.** The master action `B_t` is a function of the played arm `I_t`
(`B_t = 0` iff `I_t ∈ V_self`, otherwise `B_t = I_t`), so the law of `I_t` is `π_t` and the
whole randomness of a round is `I_t`. -/
def piDist {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (x : Option (Fin K) → ℝ)
    (q : Fin K → ℝ) : Fin K → ℝ :=
  fun i => if i ∈ Vself E then x none * q i else x (some i)

end FirstOrderFG


