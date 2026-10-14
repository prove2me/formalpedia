-- Prove2me | Definitions.Def_MFIrrev_Equilibrium_StoppingProblem
-- name    : MFIrrev_Equilibrium_StoppingProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:17.749268+00:00
-- url     : https://prove2.me/theorems/9199f7ae-abf1-4d95-af5a-5726fe966ccd
-- title:
--   §4.1.2, (4.13)–(4.14), Prop. 4.2(iii), p. 15–16 — the process X̄, the optimal stopping problem v and the hitting time τ⋆
-- statement:
--   The optimal stopping problem associated with the singular control problem.
--
--   **The process $\bar X$ (4.14).** $d\bar X_t=-(\delta-\sigma^2_{\varepsilon_t})\bar X_t\,dt+\sigma_{\varepsilon_t}\bar X_t\,dB_t$, $\bar X_0=x>0$, whose solution is
--   $$\bar X_t=x\exp\Big(-\delta t+\frac12\int_0^t\sigma^2_{\varepsilon_s}ds+\int_0^t\sigma_{\varepsilon_s}dB_s\Big).$$
--
--   **The value function (4.13).** For $Q\in(0,\infty)^2$ and the inverse demand $\eta$ of (2.7),
--   $$v(x,i)=\inf_{\tau\ge0}\bar{\mathbb E}_{(x,i)}\Big[\int_0^\tau e^{-(\rho+\delta)t}\big(\eta_{\varepsilon_t}-2c\bar X_t\big)dt+\kappa e^{-(\rho+\delta)\tau}\Big],$$
--   the infimum over all $\mathbb F$-stopping times $\tau$ with values in $[0,\infty]$, with $e^{-(\rho+\delta)\tau}=0$ on $\{\tau=\infty\}$, and $\bar{\mathbb E}_{(x,i)}$ the expectation conditioned on $\varepsilon_0=i$.
--
--   **The hitting time of Proposition 4.2(iii).** For thresholds $a_1,a_2$,
--   $$\tau^\star=\inf\{t\ge0:\bar X_t\le a_{\varepsilon_t}\}\qquad(\inf\emptyset=\infty).$$
--
--   The derivative in $x$ of the value of the singular control problem is the value of this stopping problem, which is how the paper locates the investment barriers.
--
--   **Formalization Note.** Regimes are `Fin 2` (index `0` = regime 1). $\bar X$ is given by its explicit solution. Stopping times take values in $[0,\infty]$ (`WithTop ℝ≥0`). The infimum is a real infimum over the nonempty type of stopping times; under the standing assumptions and Assumption 2.1 every payoff is integrable (the running cost is dominated by $e^{-(\rho+\delta)t}(\eta+2c\bar X_t)$ and $\mathbb E\bar X_t\le xe^{(\max_i\sigma_i^2-\delta)t}$ with $\rho+2\delta>\max_i\sigma_i^2$), and the expectations are bounded below by $-2cx/(\rho+2\delta-\max_i\sigma_i^2)$, so the infimum is not a junk value.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 15, (4.13)–(4.14); p. 16, Proposition 4.2(iii)

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- The process `X̄` of (4.14), `dX̄_t = −(δ − σ²_{ε_t})X̄_t dt + σ_{ε_t}X̄_t dB_t`, `X̄₀ = x`, given by
its explicit solution `X̄_t = x exp(−δt + ½∫₀ᵗσ²_{ε_s}ds + ∫₀ᵗσ_{ε_s}dB_s)`. -/
noncomputable def Xbar (m : Params) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (x : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  x * Real.exp (-(m.δ * t) + sigSqInt m S t ω / 2 + S.M t ω)

/-- The running cost of (4.13) at time `t ≥ 0`: `e^{−(ρ+δ)t}(η_{ε_t} − 2cX̄_t)`, with `η` the inverse
demand (2.7) at `Q`. -/
noncomputable def runCost (m : Params) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω)
    (Q : Fin 2 → ℝ) (x : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(m.ρ + m.δ) * t) * (eta m Q (S.ε t.toNNReal ω) - 2 * m.c * Xbar m S x t.toNNReal ω)

/-- The payoff of (4.13) for a (possibly infinite) random time `τ`:
`∫₀^τ e^{−(ρ+δ)t}(η_{ε_t} − 2cX̄_t)dt + κe^{−(ρ+δ)τ}`, with `e^{−(ρ+δ)·∞} = 0`, so that on `{τ = ∞}`
the payoff is `∫₀^∞ e^{−(ρ+δ)t}(η_{ε_t} − 2cX̄_t)dt`. -/
noncomputable def stopPayoff (m : Params) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω)
    (Q : Fin 2 → ℝ) (x : ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  match τ ω with
  | ⊤ => ∫ t in Ioi (0 : ℝ), runCost m S Q x t ω
  | (s : ℝ≥0) => (∫ t in (0 : ℝ)..(s : ℝ), runCost m S Q x t ω)
      + m.κ * Real.exp (-(m.ρ + m.δ) * (s : ℝ))

/-- The value function (4.13): `v(x, i) = inf_τ Ē_(x,i)[∫₀^τ e^{−(ρ+δ)t}(η_{ε_t} − 2cX̄_t)dt
+ κe^{−(ρ+δ)τ}]`, the infimum over all `𝔽`-stopping times (with values in `[0, ∞]`), the expectation
under `P` conditioned on `ε₀ = i`. Under the standing assumptions and Assumption 2.1 every payoff is
integrable and their expectations are bounded below, so this real infimum over a nonempty type is a
genuine infimum. -/
noncomputable def vStop (m : Params) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω)
    (Q : Fin 2 → ℝ) (x : ℝ) (i : Fin 2) : ℝ :=
  ⨅ τ : {τ : Ω → WithTop ℝ≥0 // IsStoppingTime S.ℱ τ},
    ∫ ω, stopPayoff m S Q x τ.1 ω ∂(Pcond P S i)

/-- The hitting time `τ⋆ = inf{t ≥ 0 : X̄_t ≤ a_{ε_t}}` of Proposition 4.2(iii) (`∞` if the set is
empty). -/
noncomputable def hitTime (m : Params) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω)
    (a : Fin 2 → ℝ) (x : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | Xbar m S x t ω ≤ a (S.ε t ω)}, (t : WithTop ℝ≥0)

end MFIrrev.Equilibrium


