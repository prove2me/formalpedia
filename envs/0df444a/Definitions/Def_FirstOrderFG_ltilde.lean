-- Prove2me | Definitions.Def_FirstOrderFG_ltilde
-- name    : FirstOrderFG_ltilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:17.074551+00:00
-- url     : https://prove2.me/theorems/7a977d17-37ad-41ec-8083-46f1eccdde04
-- title:
--   Base loss estimate $\tilde\ell_t$ (Eq. (19))
-- statement:
--   After playing $I_t$, the base learner estimates the loss of each $i\in V_{\mathrm{self}}$ by importance weighting over the whole graph:
--   $$
--   \tilde\ell_{t,i}=\frac{\ell_{t,i}\,\mathbb I\{I_t\to i\}}{Q_i^G(\pi_t)} .
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (19), p.8; Algorithm 2, line 11, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Qobs

namespace FirstOrderFG

/-- **The base loss estimate `ℓ̃_t` (Eq. (19)).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (19), p.8, and Algorithm 2, line 11:
`ℓ̃_{t,i} = ℓ_{t,i} 𝕀{I_t → i} / Q_i(π_t)` for `i ∈ V_self`, with `Q_i = Q_i^G` in the whole graph.

**Formalization Note.** `ltilde E lt π I i` takes the round's loss vector `lt = ℓ_t`, the played
distribution `π = π_t` and the played arm `I = I_t`; it is read only at `i ∈ V_self`. -/
noncomputable def ltilde {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (lt π : Fin K → ℝ)
    (I : Fin K) : Fin K → ℝ :=
  fun i => lt i * (if E I i then 1 else 0) / Qobs E π i

end FirstOrderFG


