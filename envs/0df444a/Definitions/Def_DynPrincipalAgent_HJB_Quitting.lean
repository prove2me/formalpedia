-- Prove2me | Definitions.Def_DynPrincipalAgent_HJB_Quitting
-- name    : DynPrincipalAgent_HJB_Quitting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:32:18.693924+00:00
-- url     : https://prove2.me/theorems/58f90717-185b-41a0-adf3-d91327e620c8
-- title:
--   (5.8), (6.1), (6.2), (6.5) — the quitting sequence with type switching, J_∞, u_∞, ū_∞ and V^P_∞
-- statement:
--   This file defines the principal's value when every agent may quit and the principal re-hires after each quitting.
--
--   **The quitting sequence (5.8).** Fix a type $\theta$ and $(t,x)\in D_\theta$. A triple $(\eta,Z,\zeta)$ consists of a contract $\eta\in\mathcal A^P_t$, a sensitivity $Z\in\mathcal A^A_t$ and an $\mathbb F^t$-progressively measurable $\Theta$-valued process $\zeta$ (the type of the agent in place). It belongs to $\mathcal A^{\infty,\theta}_{t,x}$ when there are quitting times $\{\tau_i\}_{i\ge0}$ and a utility process $\mathcal X$ with $\tau_0=t$, $\mathcal X_{\tau_0}=x$, $\zeta_{\tau_0}=\theta$ and, for $i\ge0$,
--   $$\tau_{i+1}=\inf\{s\ge\tau_i:\mathcal X^{\zeta_{\tau_i};\tau_i,\mathcal X_{\tau_i},\eta,Z}_s=\underline L^{\zeta_{\tau_i}}_s\}\wedge T,$$
--   $$\zeta_s=\zeta_{\tau_i},\quad \mathcal X_s=\mathcal X^{\zeta_{\tau_i};\tau_i,\mathcal X_{\tau_i},\eta,Z}_s\quad(\tau_i\le s<\tau_{i+1}),\qquad \mathcal X_{\tau_{i+1}}=R^{\zeta_{\tau_{i+1}}}_{\tau_{i+1}}\mathbf 1_{\{\tau_{i+1}<T\}}+\mathcal X^{\zeta_{\tau_i};\tau_i,\mathcal X_{\tau_i},\eta,Z}_T\mathbf 1_{\{\tau_{i+1}=T\}}.$$
--   At each quitting the principal hires a new agent of type $\zeta_{\tau_{i+1}}$ at his reservation utility.
--
--   **The value function (6.1).**
--   $$u_\infty(\theta;t,x)=\sup_{(\eta,Z,\zeta)\in\mathcal A^{\infty,\theta}_{t,x}}\mathbb E^{\zeta,Z}\Big[\int_t^T\big[I^h(\zeta_s;s,Z_s)-\eta_s\big]ds-\sum_{i\ge1}c^P_{\tau_i}\mathbf 1_{\{\tau_i<T\}}\Big]\quad\text{subject to}\quad\lim_i\tau_i=T,\ \mathcal X_{T-}=0,$$
--   where $\mathbb E^{\zeta,Z}$ is the expectation under the Girsanov measure of the effort $I^h(\zeta;\cdot,Z)$. Further,
--   $$\overline u_\infty(t)=\sup_{\theta\in\Theta}u_\infty(\theta;t,R^\theta_t)-c^P_t\ \ (6.5),\qquad V^P_\infty(\theta,t)=\sup_{R^\theta_t\le x\le\overline L^\theta_t}u_\infty(\theta;t,x),\qquad V^P_\infty(t)=\sup_\theta V^P_\infty(\theta,t)\ \ (6.2).$$
--
--   **Formalization Note.** All conditions of (5.8) and the constraints are required almost surely. The Itô integral $\int Z\,dB$ is one continuous version $J$ shared by all agents, so the $i$-th agent's utility from $\tau_i$ is $\mathcal X_{\tau_i}-\int_{\tau_i}^s[f+H]\,dr+J_s-J_{\tau_i}$. The value set records $J_\infty$ only when it is a genuine expectation: almost surely the running reward is integrable on $[t,T]$, the drift of the agents' utilities is integrable on $[t,T]$ and the quitting-cost series is summable, and the payoff is integrable under $\mathbb P^{\zeta,Z}$. These hold for every admissible triple, and without them a Bochner integral or a real series of a non-integrable or non-summable family would be $0$ and could raise $J_\infty$. $u_\infty$, $\overline u_\infty$, $V^P_\infty$ are real suprema; that the value sets are nonempty and bounded above is part of the mission's goal theorem, and that the suprema over $\Theta$ are bounded above is part of Proposition 6.2.
-- source:
--   Zhang & Zhu, A Dynamic Principal Agent Problem with One-sided Commitment, arXiv:2208.06473v3, (5.8), p. 29; (6.1)–(6.2), p. 30; (6.5), p. 31

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_DynPrincipalAgent_HJB_Model
import Definitions.Def_DynPrincipalAgent_HJB_Controls

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace DynPrincipalAgent.HJB

open Peng1990.SMP

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

namespace Model

variable {Θ : Type} [MeasurableSpace Θ] (M : Model Θ) (S : Setting Ω)

/-- The drift `r ↦ f(ζ_r; r, η_r) + H(ζ_r; r, Z_r)` of the forward utility of the agent in place, on a
path `ω`, when the type of the agent in place at time `r` is `ζ_r`. -/
noncomputable def driftζ (ζ : ℝ≥0 → Ω → Θ) (η Z : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun r => M.f (ζ r.toNNReal ω) r (η r.toNNReal ω) + M.H (ζ r.toNNReal ω) r (Z r.toNNReal ω)

/-- The quitting sequence (5.8), p. 29: `({τ_i}_{i ≥ 0}, 𝒳)` is associated with `(η, Z, ζ)` (and the
continuous version `J` of `∫ Z dB`). Almost surely, `τ_0 = t`, `𝒳_{τ_0} = x`, `ζ_{τ_0} = θ`, and for
every `i ≥ 0`, writing `𝒳^i_s = 𝒳^{ζ_{τ_i}; τ_i, 𝒳_{τ_i}, η, Z}_s` for the forward process (2.14) of the
`i`-th agent started at `τ_i` from `𝒳_{τ_i}`:
* `τ_{i+1} = inf{s ≥ τ_i : 𝒳^i_s = L̲^{ζ_{τ_i}}_s} ∧ T` (first time in `[τ_i, T]` with
  `𝒳^i_s ≤ L̲^{ζ_{τ_i}}_s`, and `T` if there is none);
* `ζ_s = ζ_{τ_i}` and `𝒳_s = 𝒳^i_s` for `τ_i ≤ s < τ_{i+1}`;
* `𝒳_{τ_{i+1}} = R^{ζ_{τ_{i+1}}}_{τ_{i+1}} 1_{τ_{i+1} < T} + 𝒳^i_T 1_{τ_{i+1} = T}`. -/
def IsAssoc (θ : Θ) (t : ℝ≥0) (x : ℝ) (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ)
    (J : ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂S.P, τ 0 ω = t ∧ X t ω = x ∧ ζ t ω = θ ∧ ∀ i : ℕ,
    τ (i + 1) ω = hittingBtwn
        (fun s ω' => M.fwd (ζ (τ i ω) ω) (τ i ω) (X (τ i ω) ω) η Z J s ω'
          - M.Lund (ζ (τ i ω) ω) s) (Iic 0) (τ i ω) M.T ω ∧
    (∀ s : ℝ≥0, τ i ω ≤ s → s < τ (i + 1) ω →
      ζ s ω = ζ (τ i ω) ω ∧
      X s ω = M.fwd (ζ (τ i ω) ω) (τ i ω) (X (τ i ω) ω) η Z J s ω) ∧
    X (τ (i + 1) ω) ω =
      if τ (i + 1) ω < M.T then M.R (ζ (τ (i + 1) ω) ω) (τ (i + 1) ω)
      else M.fwd (ζ (τ i ω) ω) (τ i ω) (X (τ i ω) ω) η Z J M.T ω

/-- `(η, Z, ζ) ∈ 𝒜^{∞,θ}_{t,x}` (p. 29) with associated `({τ_i}, 𝒳)` and a continuous version `J` of
`∫ Z dB`: `η ∈ 𝒜^P_t`, `Z ∈ 𝒜^A_t`, `ζ ∈ 𝕃⁰(𝔽^t; Θ)` (an `𝔽^t`-progressively measurable `Θ`-valued
process), almost surely the drift of the agents' forward utilities is integrable on `[t, T]`, and
(5.8) holds. -/
def InAinf (θ : Θ) (t : ℝ≥0) (x : ℝ) (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ)
    (J : ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  M.IsAP S t η ∧ M.IsAA S t Z ∧ IsProg (S.filt t) ζ ∧ M.IsStochInt S t Z J ∧
    (∀ᵐ ω ∂S.P, IntegrableOn (M.driftζ ζ η Z ω) (Icc (t : ℝ) M.T)) ∧
    M.IsAssoc S θ t x η Z ζ J τ X

/-- The quitting costs `Σ_{i ≥ 1} c^P_{τ_i} 1_{τ_i < T}` paid by the principal along a path. -/
noncomputable def quitCost (τ : ℕ → Ω → ℝ≥0) (ω : Ω) : ℝ :=
  ∑' i : ℕ, if τ (i + 1) ω < M.T then M.cP (τ (i + 1) ω) else 0

/-- The principal's realised payoff in (6.1):
`∫_t^T [I^h(ζ_s; s, Z_s) − η_s] ds − Σ_{i ≥ 1} c^P_{τ_i} 1_{τ_i < T}`. -/
noncomputable def payoffInf (t : ℝ≥0) (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ)
    (τ : ℕ → Ω → ℝ≥0) (ω : Ω) : ℝ :=
  (∫ r in Icc (t : ℝ) M.T, (M.Ih (ζ r.toNNReal ω) r (Z r.toNNReal ω) - η r.toNNReal ω))
    - M.quitCost τ ω

/-- The set of values `J_∞(t, x, η, Z, ζ)` of (6.1) over `(η, Z, ζ) ∈ 𝒜^{∞,θ}_{t,x}` subject to
`lim_i τ_i = T` and `𝒳_{T−} = 0` (almost surely). `J_∞ = E^{ζ,Z}[payoff]` is the expectation under the
Girsanov measure `ℙ^{ζ,Z}` of `α = I^h(ζ; ·, Z)` (`I` the Itô integral of `α 1_{[t,T]}`). The value is
recorded only when it is a genuine expectation: almost surely the running reward is integrable on
`[t, T]` and the quitting-cost series is summable, and the payoff is `ℙ^{ζ,Z}`-integrable. -/
def valSetInf (θ : Θ) (t : ℝ≥0) (x : ℝ) : Set ℝ :=
  {v | ∃ (η Z : ℝ≥0 → Ω → ℝ) (ζ : ℝ≥0 → Ω → Θ) (J : ℝ≥0 → Ω → ℝ) (τ : ℕ → Ω → ℝ≥0)
      (X : ℝ≥0 → Ω → ℝ) (I : ℝ≥0 → Ω → ℝ),
    M.InAinf S θ t x η Z ζ J τ X ∧
    (∀ᵐ ω ∂S.P, Tendsto (fun i => τ i ω) atTop (𝓝 M.T) ∧
      Tendsto (fun s => X s ω) (𝓝[<] M.T) (𝓝 0) ∧
      IntegrableOn (fun r : ℝ => M.Ih (ζ r.toNNReal ω) r (Z r.toNNReal ω) - η r.toNNReal ω)
        (Icc (t : ℝ) M.T) ∧
      Summable (fun i : ℕ => if τ (i + 1) ω < M.T then M.cP (τ (i + 1) ω) else 0)) ∧
    IsItoIntegral (S.filt t) S.P M.T S.B (startAt t (M.alpha ζ Z)) I ∧
    Integrable (M.payoffInf t η Z ζ τ) (M.girsanov S t (M.alpha ζ Z) I) ∧
    v = ∫ ω, M.payoffInf t η Z ζ τ ω ∂(M.girsanov S t (M.alpha ζ Z) I)}

/-- The principal's value function `u_∞(θ; t, x)` of (6.1): the supremum of `valSetInf`. -/
noncomputable def uInf (θ : Θ) (t x : ℝ) : ℝ :=
  sSup (M.valSetInf S θ t.toNNReal x)

/-- `ū_∞(t) = sup_{θ ∈ Θ} u_∞(θ; t, R^θ_t) − c^P_t` ((6.5)). -/
noncomputable def uInfBar (t : ℝ) : ℝ :=
  (⨆ θ : Θ, M.uInf S θ t (M.R θ t)) - M.cP t

/-- `V^P_∞(θ, t) = sup_{R^θ_t ≤ x ≤ L̄^θ_t} u_∞(θ; t, x)` ((6.2)). -/
noncomputable def VInf (θ : Θ) (t : ℝ) : ℝ :=
  sSup (M.uInf S θ t '' Icc (M.R θ t) (M.Lbar θ t))

/-- `V^P_∞(t) = sup_{θ ∈ Θ} V^P_∞(θ, t)` ((6.2)). -/
noncomputable def VInfAll (t : ℝ) : ℝ :=
  ⨆ θ : Θ, M.VInf S θ t

end Model

end DynPrincipalAgent.HJB


