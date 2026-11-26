-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_regularizedPayoff
-- name    : OnlineSaddlePoint_Supplement_regularizedPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:50:25.349133+00:00
-- url     : https://prove2.me/theorems/acf11079-93d0-4394-bcbf-d464653212c3
-- title:
--   Regularized payoff $\mathcal L_t=\bar{\mathcal L}_t+\frac1\eta R_X-\frac1\eta R_Y$ of SP-RFTL (Algorithm 2)
-- statement:
--   Let $\bar{\mathcal L}_1,\bar{\mathcal L}_2,\dots$ be the payoff functions observed in the online saddle point problem, let $R_X$ and $R_Y$ be regularizers for the minimizing and the maximizing player, and let $\eta>0$. The **regularized payoff** of round $t$ is
--
--   $$
--   \mathcal L_t(x,y)=\bar{\mathcal L}_t(x,y)+\frac1\eta R_X(x)-\frac1\eta R_Y(y).
--   $$
--
--   Saddle-Point Regularized Follow-the-Leader (SP-RFTL, Algorithm 2) is Saddle-Point Follow-the-Leader run on $\mathcal L_1,\mathcal L_2,\dots$: in every round both players jointly play a saddle point of $\sum_{\tau=1}^t\mathcal L_\tau$. The regularizer makes each $\mathcal L_t$ strongly convex-concave even when $\bar{\mathcal L}_t$ is only convex-concave.
--
--   **Formalization Note** An SP-RFTL run is the published SP-FTL run predicate applied to this sequence. The printed update $\sum_{\tau=1}^t\mathcal L_t$ in Algorithm 2 is read as $\sum_{\tau=1}^t\mathcal L_\tau$, as the text describes ("SP-RFTL is running SP-FTL on functions $\{\mathcal L_t\}$", p.14).
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Algorithm 2, p.11

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Regularized payoff of SP-RFTL.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, Algorithm 2,
p.11: "`𝓛_t(x, y) ← 𝓛̄_t + (1/η) R_X(x) − (1/η) R_Y(y)`". Given the observed payoffs `𝓛̄_t`, the
regularizers `R_X`, `R_Y` and the parameter `η`, this is the sequence `𝓛_t` on which SP-RFTL runs
Saddle-Point Follow-the-Leader.

**Formalization Note.** SP-RFTL (Algorithm 2) is SP-FTL (Algorithm 1) run on these regularized
payoffs, so an SP-RFTL run is `OnlineSaddlePoint.IsSPFTLRun (regularizedPayoff Lbar RX RY η) X Y T x y`.
The printed update `∑_{τ=1}^t 𝓛_t` is read as `∑_{τ=1}^t 𝓛_τ`, the only reading under which the
update is the SP-FTL update the text describes ("SP-RFTL is running SP-FTL on functions
`{𝓛_t}`", p.14). Index `0` of the payoff sequence is never used. -/
noncomputable def regularizedPayoff {E F : Type*} (Lbar : ℕ → E → F → ℝ) (RX : E → ℝ) (RY : F → ℝ) (η : ℝ) :
    ℕ → E → F → ℝ :=
  fun t x y => Lbar t x y + (1 / η) * RX x - (1 / η) * RY y

end OnlineSaddlePoint.Supplement


