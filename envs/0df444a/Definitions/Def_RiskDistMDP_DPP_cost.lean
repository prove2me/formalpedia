-- Prove2me | Definitions.Def_RiskDistMDP_DPP_cost
-- name    : RiskDistMDP_DPP_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:33.640613+00:00
-- url     : https://prove2.me/theorems/fd46e2f4-45f6-489b-bd75-afd8ef071a55
-- title:
--   Cost process $\mathfrak C=(C_t(X_t,A_t,X_{t+1}))_{t\in\mathbb N_0}$
-- statement:
--   For a state–action pair $(\mathfrak X,\mathfrak A)$, the **cost process** is
--   $$\mathfrak C:=\big(C_t(X_t,A_t,X_{t+1})\big)_{t\in\mathbb N_0},\qquad C_0\equiv0.$$
--   Problem (P) minimizes $\varsigma^{\mathfrak X,\gamma}_{0,T}(\mathfrak C)$ over $(\mathfrak X,\mathfrak A)\in\Psi$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2.5, p. 13

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_BorelMDP

set_option autoImplicit false

namespace RiskDistMDP.DPP

/-- The **cost process** `ℭ := (C_t(X_t, A_t, X_{t+1}))_{t ∈ ℕ₀}` of a pair `q = (𝔛, 𝔄)`, with
`C₀ ≡ 0` (arXiv:2203.09612v4, §2.5, p.13: "we force `C₀ ≡ 0`"). -/
def cost {Ω 𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (M : BorelMDP 𝕏 𝔸)
    (q : (ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) (t : ℕ) (ω : Ω) : ℝ :=
  if t = 0 then 0 else M.C t (q.1 t ω) (q.2 t ω) (q.1 (t + 1) ω)

end RiskDistMDP.DPP


