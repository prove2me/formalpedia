-- Prove2me | Definitions.Def_DriftVarCtrl_FixedLB_Constants
-- name    : DriftVarCtrl_FixedLB_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:15.256173+00:00
-- url     : https://prove2.me/theorems/e21d6e85-deb3-4ed2-9bed-d72211f8250b
-- title:
--   Theorem 2, pp. 12–13 — the slopes dᴸ₁, dᵁ₁, dᴸ₂, dᵁ₂ (11)–(14), conditions (7)–(10), and the static value (54)
-- statement:
--   This file defines the constants that split the cost plane in Theorem 2, the four conditions of that theorem, and the closed-form value of the static policy "always use control 1".
--
--   **The four slopes ((11)–(14), p. 13).** With $v_i = 2\mu_i/\sigma_i^2$,
--   $$d_1^L = -\frac{\sigma_2^2}{\sigma_1^2}(v_2 - v_1)\frac{U}{1 - e^{-v_1U}} + \frac{\mu_2}{\mu_1},\qquad d_1^U = -\frac{\sigma_2^2}{\sigma_1^2}(v_2 - v_1)\frac{Ue^{-v_1U}}{1 - e^{-v_1U}} + \frac{\mu_2}{\mu_1},$$
--   $$d_2^L = \frac{1}{\dfrac{\mu_1}{\mu_2} + \dfrac{\sigma_1^2}{\sigma_2^2}(v_2 - v_1)\dfrac{U}{1 - e^{-v_2U}}},\qquad d_2^U = \frac{1}{\dfrac{\mu_1}{\mu_2} + \dfrac{\sigma_1^2}{\sigma_2^2}(v_2 - v_1)\dfrac{Ue^{-v_2U}}{1 - e^{-v_2U}}}.$$
--
--   **The four conditions of Theorem 2 (p. 12).** With $\Delta h_i = h_i - h_i^*$:
--   1. (7): $\Delta h_2 \ge \max\{d_1^L\Delta h_1,\ d_1^U\Delta h_1\}$;
--   2. (8): $\Delta h_2 \le \min\{d_2^L\Delta h_1,\ d_2^U\Delta h_1\}$;
--   3. (9): $\Delta h_2 \in (d_2^L\Delta h_1,\ d_1^U\Delta h_1)$ and $\Delta h_1 > 0$;
--   4. (10): $\Delta h_2 \in (d_2^U\Delta h_1,\ d_1^L\Delta h_1)$ and $\Delta h_1 < 0$.
--
--   **The static value (54) (p. EC-4).**
--   $$V(x) = -\frac{h_1}{\mu_1}x - \frac{M\mu_1 + h_1U}{\mu_1(1 - e^{-v_1U})}e^{-v_1x} + \frac{M\mu_1 + h_1U}{\mu_1(1 - e^{-v_1U})}.$$
--
--   The conditions (7)–(10) are the regions where "always 1", "always 2", "1 then 2" and "2 then 1" are optimal (Theorem 2); the slopes are ordered by Lemma 1.
--
--   **Formalization Note.** The denominators $1 - e^{-v_iU}$ are positive because $v_i, U > 0$, and the denominators of $d_2^L, d_2^U$ are positive when $v_1 < v_2$, so no division by zero arises under the hypotheses of the mission's theorems.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 12–13, Theorem 2, conditions (7)–(10) and constants (11)–(14); p. EC-4, (54)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

namespace DriftVarCtrl.FixedLB

/-- `dᴸ₁ = −(σ₂²/σ₁²)(v₂ − v₁)·U/(1 − e^{−v₁U}) + μ₂/μ₁` ((11), Wang, Zenios, SSRN 3667132
(working paper, sha256 2d7a57ba…), p. 13). -/
noncomputable def dL1 (p : Params) : ℝ :=
  -(p.σ₂ ^ 2 / p.σ₁ ^ 2) * (v p .two - v p .one) * (p.U / (1 - Real.exp (-v p .one * p.U)))
    + p.μ₂ / p.μ₁

/-- `dᵁ₁ = −(σ₂²/σ₁²)(v₂ − v₁)·U e^{−v₁U}/(1 − e^{−v₁U}) + μ₂/μ₁` ((12), SSRN 3667132 p. 13). -/
noncomputable def dU1 (p : Params) : ℝ :=
  -(p.σ₂ ^ 2 / p.σ₁ ^ 2) * (v p .two - v p .one)
      * (p.U * Real.exp (-v p .one * p.U) / (1 - Real.exp (-v p .one * p.U)))
    + p.μ₂ / p.μ₁

/-- `dᴸ₂ = 1 / (μ₁/μ₂ + (σ₁²/σ₂²)(v₂ − v₁)·U/(1 − e^{−v₂U}))` ((13), SSRN 3667132 p. 13). -/
noncomputable def dL2 (p : Params) : ℝ :=
  1 / (p.μ₁ / p.μ₂
    + (p.σ₁ ^ 2 / p.σ₂ ^ 2) * (v p .two - v p .one) * (p.U / (1 - Real.exp (-v p .two * p.U))))

/-- `dᵁ₂ = 1 / (μ₁/μ₂ + (σ₁²/σ₂²)(v₂ − v₁)·U e^{−v₂U}/(1 − e^{−v₂U}))` ((14), SSRN 3667132
p. 13). -/
noncomputable def dU2 (p : Params) : ℝ :=
  1 / (p.μ₁ / p.μ₂
    + (p.σ₁ ^ 2 / p.σ₂ ^ 2) * (v p .two - v p .one)
      * (p.U * Real.exp (-v p .two * p.U) / (1 - Real.exp (-v p .two * p.U))))

/-- Condition (7) of Theorem 2 (SSRN 3667132 p. 12): `Δh₂ ≥ max{dᴸ₁Δh₁, dᵁ₁Δh₁}`. -/
def cond7 (p : Params) : Prop :=
  max (dL1 p * Δh p .one) (dU1 p * Δh p .one) ≤ Δh p .two

/-- Condition (8) of Theorem 2 (SSRN 3667132 p. 12): `Δh₂ ≤ min{dᴸ₂Δh₁, dᵁ₂Δh₁}`. -/
def cond8 (p : Params) : Prop :=
  Δh p .two ≤ min (dL2 p * Δh p .one) (dU2 p * Δh p .one)

/-- Condition (9) of Theorem 2 (SSRN 3667132 p. 12): `Δh₂ ∈ (dᴸ₂Δh₁, dᵁ₁Δh₁)` and `Δh₁ > 0`. -/
def cond9 (p : Params) : Prop :=
  Δh p .two ∈ Set.Ioo (dL2 p * Δh p .one) (dU1 p * Δh p .one) ∧ 0 < Δh p .one

/-- Condition (10) of Theorem 2 (SSRN 3667132 p. 12): `Δh₂ ∈ (dᵁ₂Δh₁, dᴸ₁Δh₁)` and `Δh₁ < 0`. -/
def cond10 (p : Params) : Prop :=
  Δh p .two ∈ Set.Ioo (dU2 p * Δh p .one) (dL1 p * Δh p .one) ∧ Δh p .one < 0

/-- The explicit value (54) of the static policy "always use control 1" (proof of Theorem 2 (a),
SSRN 3667132 p. EC-4):
`V(x) = −(h₁/μ₁)x − (Mμ₁ + h₁U)/(μ₁(1 − e^{−v₁U}))·e^{−v₁x} + (Mμ₁ + h₁U)/(μ₁(1 − e^{−v₁U}))`. -/
noncomputable def V54 (p : Params) (x : ℝ) : ℝ :=
  -(p.h₁ / p.μ₁) * x
    - (p.M * p.μ₁ + p.h₁ * p.U) / (p.μ₁ * (1 - Real.exp (-v p .one * p.U))) * Real.exp (-v p .one * x)
    + (p.M * p.μ₁ + p.h₁ * p.U) / (p.μ₁ * (1 - Real.exp (-v p .one * p.U)))

end DriftVarCtrl.FixedLB


