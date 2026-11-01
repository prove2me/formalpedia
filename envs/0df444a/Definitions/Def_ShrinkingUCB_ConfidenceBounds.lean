-- Prove2me | Definitions.Def_ShrinkingUCB_ConfidenceBounds
-- name    : ShrinkingUCB_ConfidenceBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:11.978384+00:00
-- url     : https://prove2.me/theorems/0af3e58c-1279-461e-acff-13238ae5672f
-- title:
--   The widths $\Delta_{t,k}$, the bounds $\mathrm{LCB}_t$, $\mathrm{UCB}_t$ and the event (4)
-- statement:
--   For a run of ConsUCB, the **width** of product $i$ is
--
--   $$
--   \Delta_{t,k}(i)=\sqrt{x_i^\top A_{t,k}^{-1}x_i},
--   $$
--
--   for $k\in\{0,\dots,K\}$; recall $A_{t,0}=A_{t-1}$, so $\Delta_{T+1,0}(i)=\sqrt{x_i^\top A_T^{-1}x_i}$. The **lower and upper confidence bounds** are
--
--   $$
--   \mathrm{LCB}_t(i)=x_i^\top\theta_t-\alpha\Delta_{t,0}(i),\qquad
--   \mathrm{UCB}_t(i)=x_i^\top\theta_t+\alpha\Delta_{t,0}(i).
--   $$
--
--   The event (4) of the source is that $\mathrm{LCB}_t(i)\le\mu(i)\le\mathrm{UCB}_t(i)$ for all $i\in[N]$ and $t\in[T+1]$.
--
--   **Formalization Note** The source writes "$k\in[K]$" for $\Delta_{t,k}$ and uses $k=0$; the definition covers every $k\ge0$.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §4.2, p.16; eq. (4), p.17

import Definitions.Def_ShrinkingUCB_ConsUCB

open Matrix

namespace ShrinkingUCB

variable {d N : ℕ}
variable (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ) (K : ℕ) (o : OutcomeTable N)

/-- The width `∆_{t,k}(i) = √(x_iᵀ A_{t,k}⁻¹ x_i)` (arXiv:1903.07844v2, §4.2, p.16), for `t ≥ 1`
and `0 ≤ k ≤ K`. In particular `∆_{T+1,0}(i) = √(x_iᵀ A_T⁻¹ x_i)`. -/
noncomputable def Delta (t k : ℕ) (i : Fin N) : ℝ :=
  √(I.x i ⬝ᵥ (innerA I tb α K o t k)⁻¹ *ᵥ I.x i)

/-- The lower confidence bound `LCB_t(i) = x_iᵀθ_t − α∆_{t,0}(i)`, p.16. -/
noncomputable def LCB (t : ℕ) (i : Fin N) : ℝ :=
  I.x i ⬝ᵥ theta I tb α K o t - α * Delta I tb α K o t 0 i

/-- The upper confidence bound `UCB_t(i) = x_iᵀθ_t + α∆_{t,0}(i)`, p.16. -/
noncomputable def UCB (t : ℕ) (i : Fin N) : ℝ :=
  I.x i ⬝ᵥ theta I tb α K o t + α * Delta I tb α K o t 0 i

/-- The event (4), p.17: `LCB_t(i) ≤ µ(i) ≤ UCB_t(i)` for all `i ∈ [N]` and `t ∈ [T + 1]`. -/
def ConfidenceHolds (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 (T + 1), ∀ i,
    LCB I tb α K o t i ≤ I.μ i ∧ I.μ i ≤ UCB I tb α K o t i

end ShrinkingUCB


