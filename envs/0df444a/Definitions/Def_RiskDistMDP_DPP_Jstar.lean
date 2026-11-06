-- Prove2me | Definitions.Def_RiskDistMDP_DPP_Jstar
-- name    : RiskDistMDP_DPP_Jstar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:23.127808+00:00
-- url     : https://prove2.me/theorems/0269767a-1931-43c7-809e-8dfb927be314
-- title:
--   Finite-horizon optimal values $J^*_{t,T}$ (4.4)
-- statement:
--   For $T\in\mathbb N$,
--   $$J^*_{t,T}:=\begin{cases}O,&t>T,\\ S_tJ^*_{t+1,T},&1\le t\le T,\end{cases}\qquad J^*_{0,T}:=H_0J^*_{1,T}.$$
--   These are computed from the model by backward induction with the Bellman operator; Theorem 4.2 shows they are the optimal values.
--
--   **Formalization Note** For $t\ge1$ the values are real via `.toReal` of $S_t$, finite under Assumption 2.13 (iv); the time-0 value `Jstar0` is in `EReal`. The value at $t=0$ of `Jstar` is $0$ and unused.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (4.4), p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_S
import Definitions.Def_RiskDistMDP_DPP_H0

set_option autoImplicit false

namespace RiskDistMDP.DPP

/-- The finite-horizon **optimal value function** `J*_{t,T}` of arXiv:2203.09612v4, (4.4), p.18:
`J*_{t,T} := O` for `t > T` and `J*_{t,T} := S_t J*_{t+1,T}` for `t ≤ T`.

**Formalization Note** Defined for `1 ≤ t`; at `t = 0` the value is `0` and is never used (the
time-0 value is `Jstar0`). The recursion takes `.toReal` of the `EReal` value of `S_t`; those
values are finite under Assumption 2.13 (iv) (Lemma 3.1 (a); p.18: "boundedness is obvious from
Lemma 3.1 (a)"). `J*_{t,T}` is computed from the data; it is not a variable pinned down by
hypotheses. -/
noncomputable def Jstar {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (T t : ℕ) : 𝕏 → ℝ :=
  if _h : 1 ≤ t ∧ t ≤ T then
    fun x => (S R t (Jstar R T (t + 1)) x).toReal
  else
    fun _ => 0
termination_by T + 1 - t
decreasing_by omega

/-- The time-0 optimal value `J*_{0,T} := H₀ J*_{1,T}` (arXiv:2203.09612v4, p.18), in `EReal`. -/
noncomputable def Jstar0 {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (T : ℕ) : EReal :=
  H0 R (Jstar R T 1)

end RiskDistMDP.DPP


