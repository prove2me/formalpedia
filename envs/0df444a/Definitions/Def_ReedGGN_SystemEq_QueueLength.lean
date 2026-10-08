-- Prove2me | Definitions.Def_ReedGGN_SystemEq_QueueLength
-- name    : ReedGGN_SystemEq_QueueLength
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:20.145985+00:00
-- url     : https://prove2.me/theorems/99ebd156-6c67-4daf-b955-700eb802c28a
-- title:
--   (2.2), (2.4)–(2.6), p. 6–7 — the number in system Q(t) and the terms G, F̄₀, W₀, M₂, A_G, I of its decomposition
-- statement:
--   Fix a sample path of the $G/GI/N$ queue (number of servers $N$, initial number $Q_0$, residual service times $\tilde\eta_i$, service times $\eta_i$, arrival times $\tau_i$ with counting process $A$, waiting times $w_i$, $\tilde w_i$). Let $F$ be the service-time distribution, given by its law $\mu$ on $\mathbb R$, and $F_0$ the residual service-time distribution, given by its law $\mu_0$. This file defines the following functions of $t\in\mathbb R$ (pp. 6–7).
--
--   1. The tails $G(x)=1-F(x)=\mu((x,\infty))$ and $\bar F_0(x)=1-F_0(x)=\mu_0((x,\infty))$, for every real $x$.
--   2. The **number of customers in the system**, equation (2.2):
--   $$Q(t)=\sum_{i=1}^{\min(Q_0,N)}1\{\tilde\eta_i>t\}+\sum_{i=1}^{(Q_0-N)^+}1\{\tilde w_i+\eta_i>t\}+\sum_{i=1}^{A(t)}1\{\tau_i+w_i+\eta_{(Q_0-N)^++i}>t\}.$$
--   3. $W_0(t)=\sum_{i=1}^{\min(Q_0,N)}\big(1\{\tilde\eta_i>t\}-\bar F_0(t)\big)$, equation (2.4).
--   4. $M_2(t)=\sum_{i=1}^{(Q_0-N)^+}\big(1\{\tilde w_i+\eta_i>t\}-G(t-\tilde w_i)\big)+\sum_{i=1}^{A(t)}\big(1\{\tau_i+w_i+\eta_{(Q_0-N)^++i}>t\}-G(t-\tau_i-w_i)\big)$, equation (2.5).
--   5. $A_G(t)=\int_0^t G(t-s)\,dA(s)=\sum_{i=1}^{A(t)}G(t-\tau_i)$, equation (2.6).
--   6. $I(t)=\min(Q_0,N)\,\bar F_0(t)+(Q_0-N)^+G(t)$, p. 7.
--
--   $Q$ counts every customer in the system (in service or waiting); the number waiting is $(Q-N)^+$. $W_0$ and $M_2$ are the centred fluctuation terms, $A_G(t)$ is the conditional mean number in the $G/GI/\infty$ queue fed by the same arrivals, and $I$ is the mean contribution of the initial customers.
--
--   **Formalization Note** $G$ and $\bar F_0$ are defined on all of $\mathbb R$: when $\mu$ is carried by $[0,\infty)$, $G(x)=1$ for $x<0$, which is the value the paper uses for $G(t-\tau_i-w_i)$ while customer $i$ is still waiting. $(Q_0-N)^+$ is truncated subtraction of natural numbers. $Q(t)$ is a natural number and is cast to $\mathbb R$ where it is compared with real quantities. The Stieltjes integral (2.6) is against the counting measure of the arrival times, which puts unit mass at each $\tau_i$, $i\ge1$ ($A(0-)=0$); its arrivals in the closed interval $[0,t]$ are exactly $i=1,\dots,A(t)$, so (2.6) is the finite sum written above.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 6, Eq. (2.2); p. 7, Eqs. (2.4), (2.5), (2.6) and the definition of I(t) after (2.7)

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_SamplePath

namespace ReedGGN.SystemEq

open MeasureTheory

/-- The tail `G(x) = 1 − F(x) = μ((x, ∞))` of the service-time distribution `F`, whose law is
the probability measure `μ` on `ℝ` (p. 6). It is defined for every real `x`; when `μ` is
carried by `[0, ∞)`, `G(x) = 1` for `x < 0`. -/
noncomputable def G (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Set.Ioi x)).toReal

/-- The tail `F̄₀(x) = 1 − F₀(x) = μ₀((x, ∞))` of the residual service-time distribution
`F₀`, whose law is `μ₀` (p. 6). -/
noncomputable def F0bar (μ₀ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ₀ (Set.Ioi x)).toReal

/-- The number of customers in the system at time `t`, equation (2.2), p. 6:
`Q(t) = Σ_{i=1}^{min(Q₀,N)} 1{η̃_i > t} + Σ_{i=1}^{(Q₀−N)⁺} 1{w̃_i + η_i > t}
        + Σ_{i=1}^{A(t)} 1{τ_i + w_i + η_{(Q₀−N)⁺+i} > t}`.
Here `P.Q₀ - P.N` is truncated subtraction in `ℕ`, i.e. `(Q₀ − N)⁺`. -/
noncomputable def Q (P : SamplePath) (t : ℝ) : ℕ :=
  ((Finset.Icc 1 (min P.Q₀ P.N)).filter (fun i => t < P.ηt i)).card +
  ((Finset.Icc 1 (P.Q₀ - P.N)).filter (fun i => t < P.wt i + P.η i)).card +
  ((Finset.Icc 1 (P.A t)).filter
    (fun i => t < P.τ i + P.w i + P.η (P.Q₀ - P.N + i))).card

/-- `W₀(t) = Σ_{i=1}^{min(Q₀,N)} (1{η̃_i > t} − F̄₀(t))`, equation (2.4), p. 7. -/
noncomputable def W0 (μ₀ : Measure ℝ) (P : SamplePath) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (min P.Q₀ P.N), ((if t < P.ηt i then (1 : ℝ) else 0) - F0bar μ₀ t)

/-- `M₂(t)`, equation (2.5), p. 7:
`Σ_{i=1}^{(Q₀−N)⁺} (1{w̃_i + η_i > t} − G(t − w̃_i))
  + Σ_{i=1}^{A(t)} (1{τ_i + w_i + η_{(Q₀−N)⁺+i} > t} − G(t − τ_i − w_i))`. -/
noncomputable def M2 (μ : Measure ℝ) (P : SamplePath) (t : ℝ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N),
      ((if t < P.wt i + P.η i then (1 : ℝ) else 0) - G μ (t - P.wt i))) +
  ∑ i ∈ Finset.Icc 1 (P.A t),
      ((if t < P.τ i + P.w i + P.η (P.Q₀ - P.N + i) then (1 : ℝ) else 0) -
        G μ (t - P.τ i - P.w i))

/-- `A_G(t) = ∫_0^t G(t − s) dA(s)`, equation (2.6), p. 7. The Stieltjes integral against the
counting process `A` (with `A(0−) = 0`) puts unit mass at each arrival time `τ_i`, `i ≥ 1`,
and the arrivals in the closed interval `[0, t]` are exactly `i = 1, …, A(t)`; so it is the
finite sum `Σ_{i=1}^{A(t)} G(t − τ_i)`. -/
noncomputable def AG (μ : Measure ℝ) (P : SamplePath) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (P.A t), G μ (t - P.τ i)

/-- `I(t) = min(Q₀, N) F̄₀(t) + (Q₀ − N)⁺ G(t)`, p. 7. -/
noncomputable def I (μ μ₀ : Measure ℝ) (P : SamplePath) (t : ℝ) : ℝ :=
  (min P.Q₀ P.N : ℕ) * F0bar μ₀ t + (P.Q₀ - P.N : ℕ) * G μ t

end ReedGGN.SystemEq


