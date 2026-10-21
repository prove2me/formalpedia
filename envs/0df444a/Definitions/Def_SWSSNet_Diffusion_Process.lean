-- Prove2me | Definitions.Def_SWSSNet_Diffusion_Process
-- name    : SWSSNet_Diffusion_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:02.436129+00:00
-- url     : https://prove2.me/theorems/710ecb21-042e-4711-8a97-6729ab1bbeb5
-- title:
--   §4.2 and §6.1, pp. 18, 25 — Σ, stationary Markov controls, strong transition laws, transience, V_{ε,S}
-- statement:
--   This module sets up the limiting controlled diffusion
--   $$
--   dX_t=b(X_t,U_t)\,dt+\Sigma\,dW_t,\qquad \Sigma=\mathrm{diag}\big(\sqrt{2\lambda_1},\dots,\sqrt{2\lambda_I}\big), \qquad (41)
--   $$
--   of the tree network, with $W$ an $I$-dimensional standard Brownian motion and $b$ the drift (42). It defines:
--
--   1. **Stationary Markov controls** $U_t=v(X_t)$: Borel measurable maps $v:\mathbb R^I\to\Delta_I\times\Delta_J$.
--   2. The vector field $x\mapsto b(x,v(x))$ under such a control, for the drift (42) with a given constant vector ($h$ of (12), or $-\vartheta_pp$ for the recentred drift).
--   3. **Existence of strong solutions** from every initial point.
--   4. **Transition probabilities** $P_t(x,\cdot)$ of the strong solutions. On every probability space carrying a standard Brownian motion, every strong solution started at $x$ has law $P_t(x,\cdot)$ at time $t$.
--   5. **Transience.** Every strong solution, from every initial point, satisfies $|X_t|\to\infty$ almost surely.
--   6. The Lyapunov function of p. 25: $V_{\varepsilon,S}(x)=\exp\big(\varepsilon\|x\|_S^2(1+\|x\|_S^2)^{-1/2}\big)$ with $\|x\|_S^2=\langle x,Sx\rangle$.
--
--   **Formalization Note** States are `EuclideanSpace ℝ (Fin I)`. Strong solutions are the published `UnifErgHW.Diffusion.IsStrongSolution`: continuous paths satisfying $X_t=x+\int_0^tb(X_s)\,ds+\Sigma W_t$ for every $\omega$, measurable time marginals, and each marginal almost surely a measurable function of the Brownian path stopped at that time. The paper does not define "transient". The definition used here, $|X_t|\to\infty$ a.s. for every strong solution, is the standard notion for a nondegenerate diffusion.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 18 ((41), U_sm), p. 25 (V_{ε,S})

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory Filter
open scoped NNReal BigOperators

namespace SWSSNet.Diffusion

/-!
Hmedi, Arapostathis & Pang, arXiv:2009.01942v3, §4.2 (p. 18) and §6.1 (p. 25): the limiting
controlled diffusion `dX_t = b(X_t, U_t) dt + Σ dW_t` (41) under stationary Markov controls, its
strong solutions and transition laws, transience, and the Lyapunov function `V_{ε,S}`.

Strong solutions are the published `UnifErgHW.Diffusion.IsStrongSolution` (integral form of the
additive-noise SDE, measurable time marginals, each marginal a measurable functional of the stopped
Brownian path).
-/

variable {I J : ℕ}

/-- `Σ := diag(√(2λ_1), …, √(2λ_I))` of (41), p. 18. -/
noncomputable def Sigma (N : TreeNetwork I J) : Matrix (Fin I) (Fin I) ℝ :=
  Matrix.diagonal fun i => Real.sqrt (2 * N.lam i)

/-- A stationary Markov control `v ∈ U_sm` (p. 18): a Borel measurable map `ℝ^I → U = ∆_I × ∆_J`. -/
def IsMarkovControl (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)) : Prop :=
  Measurable v ∧ ∀ x, IsControlValue (v x)

/-- The drift `x ↦ b(x, v(x))` under the stationary Markov control `U_t = v(X_t)`, for the drift
(42) with constant vector `hv` (`hv = h` of (12) gives the paper's `b`). -/
noncomputable def markovDrift (N : TreeNetwork I J) (hv : Fin I → ℝ)
    (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)) :
    EthierKurtz.SDEState I → EthierKurtz.SDEState I :=
  fun x => driftH N hv (v x) x

/-- Strong solutions of `dX_t = b(X_t) dt + σ dW_t` exist from every initial point: for every
`x` there is a probability space carrying a standard Brownian motion `B` and a strong solution `X`
driven by `B` with `X_0 = x`. -/
def HasStrongSolutions (b : EthierKurtz.SDEState I → EthierKurtz.SDEState I)
    (σ : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  ∀ x : EthierKurtz.SDEState I, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pr : Measure Ω)
    (_ : IsProbabilityMeasure Pr) (B X : ℝ≥0 → Ω → EthierKurtz.SDEState I),
    EthierKurtz.IsStandardBrownian Pr B ∧ UnifErgHW.Diffusion.IsStrongSolution Pr b σ B X x

/-- `P` is the transition probability `P_t(x, ·)` of the strong solutions of
`dX_t = b(X_t) dt + σ dW_t`: on every probability space carrying a standard Brownian motion `B`,
every strong solution driven by `B` and started at `x` has law `P t x` at time `t`. -/
def IsStrongTransition (b : EthierKurtz.SDEState I → EthierKurtz.SDEState I)
    (σ : Matrix (Fin I) (Fin I) ℝ)
    (P : ℝ≥0 → EthierKurtz.SDEState I → Measure (EthierKurtz.SDEState I)) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState I) (x : EthierKurtz.SDEState I),
    EthierKurtz.IsStandardBrownian Pr B → UnifErgHW.Diffusion.IsStrongSolution Pr b σ B X x →
    ∀ t, Pr.map (X t) = P t x

/-- Transience of `dX_t = b(X_t) dt + σ dW_t`: every strong solution, driven by a standard
Brownian motion and started at any point, satisfies `|X_t| → ∞` almost surely as `t → ∞`. -/
def IsTransient (b : EthierKurtz.SDEState I → EthierKurtz.SDEState I)
    (σ : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B X : ℝ≥0 → Ω → EthierKurtz.SDEState I) (x : EthierKurtz.SDEState I),
    EthierKurtz.IsStandardBrownian Pr B → UnifErgHW.Diffusion.IsStrongSolution Pr b σ B X x →
    ∀ᵐ ω ∂Pr, Tendsto (fun t => ‖X t ω‖) atTop atTop

/-- `V_{ε,S}(x) := exp(ε‖x‖²_S (1 + ‖x‖²_S)^{−1/2})` with `‖x‖²_S = ⟨x, Sx⟩` (p. 25). -/
noncomputable def lyapVS (ε : ℝ) (S : Matrix (Fin I) (Fin I) ℝ) (x : EthierKurtz.SDEState I) : ℝ :=
  Real.exp (ε * (WithLp.ofLp x ⬝ᵥ S *ᵥ WithLp.ofLp x) /
    Real.sqrt (1 + WithLp.ofLp x ⬝ᵥ S *ᵥ WithLp.ofLp x))

end SWSSNet.Diffusion


