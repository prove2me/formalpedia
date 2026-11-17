-- Prove2me | Definitions.Def_FirstOrderFG_Supplement_Alg1_update
-- name    : FirstOrderFG_Supplement_Alg1_update
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:38:41.681508+00:00
-- url     : https://prove2.me/theorems/f88ea566-a026-4d76-bb1c-bfcb2d3b0403
-- title:
--   Ordinary-simplex EXP3 update of Algorithm 1
-- statement:
--   For a current distribution $p_t$, loss estimate $\widehat\ell_t$, and learning rate $\eta$, Algorithm 1 chooses
--
--   $$
--   p_{t+1}\in\arg\min_{p\in\Delta_K}\left\{\eta\langle p,\widehat\ell_t\rangle+D_h(p,p_t)\right\},
--   $$
--
--   where $D_h$ is the negative-entropy Bregman divergence. The feasible region is the ordinary simplex, not Algorithm 2's clipped simplex.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (1), p.4; Algorithm 1, line 5, p.7

import Mathlib

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **The ordinary-simplex EXP3 update of Algorithm 1.** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Eq. (1), p.4, and Algorithm 1, line 5, p.7:
`argmin_{r ∈ Δ_K} {η ⟨r, ℓ̂_t⟩ + D_h(r,p_t)}`.

**Formalization Note.** This is the ordinary simplex `Δ_K`, not Algorithm 2's clipped
simplex. The argmin is `Classical.epsilon` over `IsMinOn`; negative-entropy divergence is
written explicitly over all `K` arms. -/
noncomputable def Alg1.update {K : ℕ} (η : ℝ) (p lt : Fin K → ℝ) : Fin K → ℝ :=
  Classical.epsilon fun pn =>
    pn ∈ {r : Fin K → ℝ | (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1} ∧
      IsMinOn
        (fun r => η * ∑ i, r i * lt i +
          ∑ i, (r i * Real.log (r i / p i) - r i + p i))
        {r : Fin K → ℝ | (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1} pn

end FirstOrderFG.Supplement


