-- Prove2me | Definitions.Def_RiskDistMDP_DPP_Jpol
-- name    : RiskDistMDP_DPP_Jpol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:27.993243+00:00
-- url     : https://prove2.me/theorems/1986dcc2-83d7-4be1-a3c0-e3f9f4965dac
-- title:
--   Finite-horizon policy values $J^{\mathfrak p}_{t,T}$ (4.1)
-- statement:
--   For $T\in\mathbb N$ and $\mathfrak p\in\Pi$, with $O(x):=0$,
--   $$J^{\mathfrak p}_{t,T}:=\begin{cases}O,&t>T,\\ H^{\mathfrak p}_tJ^{\mathfrak p}_{t+1,T},&1\le t\le T,\end{cases}\qquad J^{\mathfrak p}_{0,T}:=H_0J^{\mathfrak p}_{1,T},$$
--   so $J^{\mathfrak p}_{t,T}=H^{\mathfrak p}_t\circ\cdots\circ H^{\mathfrak p}_TO$. By Lemma 3.3 these are the DRMs of a Markov pair associated with $\mathfrak p$.
--
--   **Formalization Note** For $t\ge1$ the values are real, via `.toReal` of the `EReal` value of $H^{\mathfrak p}_t$; they are finite under Assumption 2.13 (iv) (Lemma 3.1). The value at $t=0$ of `Jpol` is $0$ and unused; the time-0 value is `Jpol0`, in `EReal`.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (4.1), p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_H
import Definitions.Def_RiskDistMDP_DPP_H0

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The finite-horizon **value function of a Markovian policy** `J^𝔭_{t,T}` of
arXiv:2203.09612v4, (4.1), p.18: `J^𝔭_{t,T} := O` for `t > T` and `J^𝔭_{t,T} := H^𝔭_t J^𝔭_{t+1,T}`
for `t ≤ T`, where `O(x) := 0`; so `J^𝔭_{t,T} = H^𝔭_t ∘ ⋯ ∘ H^𝔭_T O`.

**Formalization Note** Defined for `1 ≤ t`; at `t = 0` the value is `0` and is never used (the
time-0 value is `Jpol0`). The recursion takes `.toReal` of the `EReal` value of `H^𝔭_t`; those
values are finite under Assumption 2.13 (iv) (Lemma 3.1, `lemma_3_1`). -/
noncomputable def Jpol {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (T t : ℕ) : 𝕏 → ℝ :=
  if _h : 1 ≤ t ∧ t ≤ T then
    fun x => (H R 𝔭 t (Jpol R 𝔭 T (t + 1)) x).toReal
  else
    fun _ => 0
termination_by T + 1 - t
decreasing_by omega

/-- The time-0 value of a Markovian policy, `J^𝔭_{0,T} := H₀ J^𝔭_{1,T}` (arXiv:2203.09612v4,
p.18), in `EReal`. -/
noncomputable def Jpol0 {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (T : ℕ) : EReal :=
  H0 R (Jpol R 𝔭 T 1)

end RiskDistMDP.DPP


