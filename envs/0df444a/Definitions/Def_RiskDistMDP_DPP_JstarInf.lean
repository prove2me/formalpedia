-- Prove2me | Definitions.Def_RiskDistMDP_DPP_JstarInf
-- name    : RiskDistMDP_DPP_JstarInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:30.786201+00:00
-- url     : https://prove2.me/theorems/04329f64-7b5d-49a7-b01c-02b40d5e3e64
-- title:
--   Infinite-horizon optimal values $J^*_{t,\infty}$ (5.4)
-- statement:
--   $$J^*_{0,\infty}:=\lim_{T\to\infty}J^*_{0,T},\qquad J^*_{t,\infty}(x):=\lim_{T\to\infty}J^*_{t,T}(x),\quad x\in\mathbb X,\ t\in\mathbb N.$$
--
--   **Formalization Note** `limUnder atTop`, pointwise, in $\mathbb R$ for $t\ge1$ and in `EReal` at time $0$; Lemma 5.3 states that the limits exist. $J^*_{t,\infty}$ is not defined as a fixed point of $S_t$, so the Bellman equation of Theorem 5.5 is a theorem, not a definition.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (5.4), p. 22

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Jstar

set_option autoImplicit false

open Filter

namespace RiskDistMDP.DPP

/-- The infinite-horizon **optimal value function** `J*_{t,∞}(x) := lim_{T→∞} J*_{t,T}(x)`,
`x ∈ 𝕏`, `t ∈ ℕ` (arXiv:2203.09612v4, (5.4), p.22).

**Formalization Note** `limUnder atTop` in `ℝ`, pointwise in `x`, for `t ≥ 1`. It is a junk value
where the sequence diverges; Lemma 5.3 (`lemma_5_3`) states uniform convergence. It is not defined
as a fixed point of `S`, so the Bellman equation of Theorem 5.5 (a) is not definitional. -/
noncomputable def JstarInf {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (t : ℕ) (x : 𝕏) : ℝ :=
  limUnder atTop fun T => Jstar R T t x

/-- `J*_{0,∞} := lim_{T→∞} J*_{0,T}` (arXiv:2203.09612v4, (5.4), p.22), as a `limUnder atTop` in
`EReal`. -/
noncomputable def Jstar0Inf {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) : EReal :=
  limUnder atTop fun T => Jstar0 R T

end RiskDistMDP.DPP


