-- Prove2me | Definitions.Def_ExitGamePrivate_BestResponse
-- name    : ExitGamePrivate_BestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:38.116992+00:00
-- url     : https://prove2.me/theorems/c719fde4-f863-42c5-bd26-badb436a68de
-- title:
--   Best-response value functions $v$ (4.15), $\tilde v$ (4.17), and the stopping set $\mathcal S^\theta_{\tilde v}$
-- statement:
--   Against the equilibrium strategy of the opponent, a player of type $\theta$ faces a Markovian optimal stopping problem in the pair $(X_t,A_t)$ started at $(x,a)$, with $A=A^{x,a}$ (§4.4, p.17):
--   $$v(x,a;\theta)=\sup_{\sigma\in\mathcal T(\mathcal F_t)}E_{xa}\Big[\int_0^\sigma e^{-rs-A_s}D(X_s)\,ds+\theta e^{-r\sigma-A_\sigma}+\int_0^\sigma e^{-rs-A_s}m(X_s)\lambda(X_s,Y(A_s))\,ds\Big], \tag{4.15}$$
--   $$\tilde v(x,a;\theta)=\sup_{\sigma\in\mathcal T(\mathcal F_t)}E_{xa}\Big[\int_0^\sigma e^{-rs-A_s}\big(D(X_s)-r\theta+\lambda(X_s,Y(A_s))(m(X_s)-\theta)\big)\,ds\Big], \tag{4.17}$$
--   and the paper notes $v=\tilde v+\theta e^{-a}$. The **stopping set** is
--   $$\mathcal S^\theta_{\tilde v}=\{(x,a)\in\mathcal I\times[0,\infty):\tilde v(x,a;\theta)=0\}.$$
--
--   These value functions connect the game to optimal stopping: by Lemma 4.2, $v(x,0;\theta)$ is the best payoff a type-$\theta$ player can obtain against the equilibrium strategy.
--
--   **Formalization Note** The suprema run over $[0,\infty]$-valued $(\mathcal F_t)$-stopping times, and on $\{\sigma=\infty\}$ the term $\theta e^{-r\sigma-A_\sigma}$ is $0$. Proposition 4.10 prints $\mathcal I\times[0,\infty]$ for the stopping set; $A$ is finite, $\tilde v$ is defined only for finite $a$, and Corollary 4.15 and §4.5 use $\mathcal I\times[0,\infty)$, which is what is defined here.
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, §4.4 p.17 ((4.15), (4.17)), Proposition 4.10 p.17 (S^θ_ṽ), §4.5 p.17

import Mathlib
import Definitions.Def_ExitGamePrivate_Belief

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ExitGamePrivate

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω)

/-- The objective of the best-response problem (4.15), p.17, for a stopping time `σ`, from
`(X₀, A₀) = (x, a)` (`A = A^{x,a}`):
`E_{xa}[∫_0^σ e^{-rs-A_s} D(X_s) ds + θ e^{-rσ-A_σ} + ∫_0^σ e^{-rs-A_s} m(X_s) λ(X_s, Y(A_s)) ds]`.
On `{σ = ∞}` the middle term is `0`. -/
def vObj (α : ℝ → ℝ) (x a θ : ℝ) (σ : Ω → WithTop ℝ≥0) : ℝ :=
  ∫ ω, ((∫ s in window (σ ω),
      Real.exp (-(G.r * s) - G.Asol α x a s ω) * G.D (G.X x s ω)) +
    θ * (disc G.r (σ ω) * Real.exp (-G.Asol α x a (((σ ω).untopD 0 : ℝ≥0) : ℝ) ω)) +
    ∫ s in window (σ ω), Real.exp (-(G.r * s) - G.Asol α x a s ω) * G.m (G.X x s ω) *
      G.lam α (G.X x s ω) (G.Y (G.Asol α x a s ω))) ∂G.P

/-- The best-response value function (4.15), p.17:
`v(x, a; θ) = sup_{σ ∈ 𝒯(Fₜ)} E_{xa}[…]` (see `vObj`). -/
def v (α : ℝ → ℝ) (x a θ : ℝ) : ℝ :=
  ⨆ σ : {σ : Ω → WithTop ℝ≥0 // IsStoppingTime G.filt σ}, G.vObj α x a θ σ.1

/-- The objective of (4.17), p.17:
`E_{xa}[∫_0^σ e^{-rs-A_s}(D(X_s) − rθ + λ(X_s, Y(A_s))(m(X_s) − θ)) ds]`. -/
def vtilObj (α : ℝ → ℝ) (x a θ : ℝ) (σ : Ω → WithTop ℝ≥0) : ℝ :=
  ∫ ω, (∫ s in window (σ ω), Real.exp (-(G.r * s) - G.Asol α x a s ω) *
      (G.D (G.X x s ω) - G.r * θ +
        G.lam α (G.X x s ω) (G.Y (G.Asol α x a s ω)) * (G.m (G.X x s ω) - θ))) ∂G.P

/-- The reduced value function (4.17), p.17: `ṽ(x, a; θ) = sup_{σ ∈ 𝒯(Fₜ)} E_{xa}[…]`
(see `vtilObj`); the paper notes `v = ṽ + θe^{-a}`. -/
def vtil (α : ℝ → ℝ) (x a θ : ℝ) : ℝ :=
  ⨆ σ : {σ : Ω → WithTop ℝ≥0 // IsStoppingTime G.filt σ}, G.vtilObj α x a θ σ.1

/-- The stopping set of Proposition 4.10, p.17: `S^θ_ṽ = {(x, a) ∈ 𝓘 × [0, ∞) : ṽ(x, a; θ) = 0}`.

**Formalization Note** Proposition 4.10 prints `𝓘 × [0, ∞]`; `A` is finite, `ṽ` is only defined
for finite `a`, and Corollary 4.15 and §4.5 (p.17, `C^θ_ṽ = 𝓘 × [0, ∞) \ S^θ_ṽ`) use
`𝓘 × [0, ∞)`. -/
def Sstop (α : ℝ → ℝ) (θ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ G.I ∧ 0 ≤ p.2 ∧ G.vtil α p.1 p.2 θ = 0}

end Model

end ExitGamePrivate


