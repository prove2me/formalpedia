-- Prove2me | Definitions.Def_DemandResponse_SecondBest_ClosedForm
-- name    : DemandResponse_SecondBest_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:41:59.09104+00:00
-- url     : https://prove2.me/theorems/68d73add-f42c-4c6f-b75d-d823700dbc65
-- title:
--   Closed-form ingredients of the second-best value: $q_t(z)$, $m_{SB}$, $v(0,X_0)$, $L_0$ and $U$
-- statement:
--   With the parameters and the Hamiltonian $H_v$ of the model (definition `DemandResponse.SecondBest.Hamiltonian`), and $\delta=\kappa-\theta$, define for $t\in\mathbb R$ and $z\in\mathbb R$:
--
--   1. the producer's unit cost of volatility under the payment rate $z$,
--   $$q_t(z):=h+rz^2+p\big(z-\delta(T-t)\big)^2;$$
--   2. the rate
--   $$m_{SB}(t):=\frac12\bar\mu\,\delta^2(T-t)^2-\frac12\inf_{z\in\mathbb R}\Big\{\bar\mu\big(z^-+\delta(T-t)\big)^2-2H_v\big(-q_t(z)\big)\Big\};$$
--   3. the producer's certainty equivalent at the initial state,
--   $$v(0,X_0):=\delta TX_0+\int_0^Tm_{SB}(s)\,ds;$$
--   4. the consumer's certainty equivalent of the reservation utility, $L_0:=-\frac1r\log(-R_0)$;
--   5. the producer's utility $U(x):=-e^{-px}$.
--
--   These are the quantities of Proposition 3.2 (i), which states that the second-best value equals $U(v(0,X_0)-L_0)$.
--
--   **Formalization Note.** The paper prints $-2H_m(-q(z))$ inside the infimum of $m_{SB}$. This is a misprint for $-2H_v(-q(z))$: with $H_m$ the infimand tends to $-\infty$ as $z\to+\infty$ whenever $\bar\mu>0$, and the proof (Lemma A.1 and (A.11), pp. 29-30) uses $F_0(q)=-2H_v(-q)$. The infimand is non-negative (since $q_t(z)\ge h>0$ and $-2H_v(-q)=\inf_b\{c_2(b)+q|\sigma(b)|^2\}\ge0$ for $q\ge0$), so the real infimum is a genuine infimum. The time integral is an interval integral; $m_{SB}$ is continuous in $t$.
-- source:
--   arXiv:1810.09063v3, Proposition 3.2 (i) (p. 11) and the definition of L_0 (p. 8), U in (2.4) (p. 8)

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

variable {N d : ℕ}

/-- The producer's unit cost of volatility at time `t` under the payment rate `z`,
`q_t(z) := h + r z² + p (z - δ(T - t))²` (Prop. 3.2 (i), p. 11). -/
def qSB (P : Params N d) (t z : ℝ) : ℝ :=
  P.h + P.r * z ^ 2 + P.p * (z - delta P * (P.T - t)) ^ 2

/-- `m_SB(t) := ½ μ̄ δ² (T-t)² - ½ inf_{z ∈ ℝ} { μ̄ (z⁻ + δ(T-t))² - 2 H_v(-q_t(z)) }`
(Prop. 3.2 (i), p. 11, with the printed `H_m` corrected to `H_v`). The infimand is `≥ 0`, so the real
infimum is a genuine infimum of a bounded-below set. -/
noncomputable def mSB (P : Params N d) (t : ℝ) : ℝ :=
  (1 / 2) * muBar P * delta P ^ 2 * (P.T - t) ^ 2
    - (1 / 2) * ⨅ z : ℝ, (muBar P * (negp z + delta P * (P.T - t)) ^ 2 - 2 * Hv P (-(qSB P t z)))

/-- The producer's certainty equivalent at the initial state,
`v(0, X₀) = δ T X₀ + ∫₀ᵀ m_SB(s) ds` (Prop. 3.2 (i), p. 11). -/
noncomputable def v0 (P : Params N d) : ℝ :=
  delta P * P.T * P.X0 + ∫ s in (0 : ℝ)..P.T, mSB P s

/-- The consumer's certainty equivalent of the reservation utility, `L₀ := -(1/r) log(-R₀)` (p. 8). -/
noncomputable def L0 (P : Params N d) : ℝ := -(1 / P.r) * Real.log (-P.R0)

/-- The producer's CARA utility `U(x) := -e^{-p x}` ((2.4), p. 8). -/
noncomputable def Uprod (P : Params N d) (x : ℝ) : ℝ := -Real.exp (-P.p * x)

end DemandResponse.SecondBest


