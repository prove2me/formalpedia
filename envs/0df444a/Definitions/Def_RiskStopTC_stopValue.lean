-- Prove2me | Definitions.Def_RiskStopTC_stopValue
-- name    : RiskStopTC_stopValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:15.300536+00:00
-- url     : https://prove2.me/theorems/3a529d35-8737-4961-9027-22f6b2052c1b
-- title:
--   The objective $\rho_{0,T}(Z_\tau)$ of the stopping problem (5.15), as a real number
-- statement:
--   For a stopping time $\tau$, the objective of the risk-averse stopping problem
--   $$\max_{\tau\in\mathfrak T_m}\rho_{0,T}(Z_\tau)\tag{5.15}$$
--   is the number $\rho_{0,T}(Z_\tau)$. Since $\mathcal F_0$ is trivial, $\rho_{0,T}(Z_\tau)$ is $\mathcal F_0$-measurable, hence constant, and it is identified with that real number.
--
--   **Formalization Note** Defined as $\int\rho_{0,T}(Z_\tau)\,dP$; for a constant function and a probability measure $P$ this is the constant.
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, (5.15), p.20; p.17 ("Since F0 is trivial, the corresponding functional ρ0,T : ZT → R is real valued")

import Mathlib
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV

namespace RiskStopTC

open MeasureTheory

/-- **The objective of (5.15).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, (5.15), p.20:
"max_{τ∈𝔗m} ρ0,T(Zτ)", and p.17: "Since F0 is trivial, the corresponding functional
ρ0,T : ZT → R is real valued."

`stopValue P ϱ Z T τ = ∫ ρ_{0,T}(Z_τ) dP`, the real number `ρ_{0,T}(Z_τ)`.

**Formalization Note.** `ρ_{0,T}(Z_τ)` is an `F₀`-measurable function, hence constant when `F₀` is
trivial (every statement of the mission assumes it), and its integral against the probability
measure `P` is that constant. -/
noncomputable def stopValue {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure[mΩ] Ω)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (Z : ℕ → Ω → ℝ) (T : ℕ) (τ : Ω → WithTop ℕ) : ℝ :=
  ∫ ω, nested ϱ 0 T (stoppedRV Z τ T) ω ∂P

end RiskStopTC


