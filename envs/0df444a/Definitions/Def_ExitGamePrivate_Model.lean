-- Prove2me | Definitions.Def_ExitGamePrivate_Model
-- name    : ExitGamePrivate_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:23.69559+00:00
-- url     : https://prove2.me/theorems/8d7ab941-2bb0-4637-ada6-608528544e9d
-- title:
--   Exit-game model: $r, D, M, F$, $m$, $d$, $a_\theta$, Assumptions 2.3, 3.1, 4.1, and the single-player problem (3.1)–(3.2)
-- statement:
--   The exit game adds to the diffusion an interest rate $r$, a duopoly profit flow $D$, a monopoly profit flow $M$, the ends $\theta_L\le\theta_U$ of the support of the exit values, and their common cumulative distribution function $F$ (pp.5–6, 10). From these the paper defines
--   $$m(x)=E_x\Big[\int_0^\infty e^{-rs}M(X_s)\,ds\Big],\qquad d(x)=E_x\Big[\int_0^\infty e^{-rs}D(X_s)\,ds\Big],\qquad a_\theta(x)=\frac{\theta-d(x)}{\varphi(x)}. \tag{3.4}$$
--
--   The standing assumptions are:
--   1. **Assumption 2.3** (p.6): $D,M:\mathcal I\to[0,\infty)$ are continuous, increasing and bounded, $M>D$, $\inf_{x\in\mathcal I}m(x)>\theta_U$, and $r>0$.
--   2. **Assumption 3.1** (p.8), for a function $\alpha$: (i) for each $\theta\in[\theta_L,\theta_U]$ there is a critical value $c(\theta)\in\mathcal I\cup\{x_U\}$ with $D(x)\le r\theta$ for $x<c(\theta)$ and $D(x)>r\theta$ for $x>c(\theta)$; (ii) $a_\theta$ attains a unique global maximum over $\mathcal I$ at $\alpha(\theta)\in\mathcal I$, is differentiable there and is increasing for $x<\alpha(\theta)$; (iii) $\alpha$ is strictly increasing on $[\theta_L,\theta_U]$.
--   3. **Assumption 4.1** (p.10, with the support of Assumption 2.2): $F$ is continuous, strictly increasing on $[\theta_L,\theta_U]$, $F=0$ on $(-\infty,\theta_L]$ and $F=1$ on $[\theta_U,\infty)$.
--
--   The **single-player problem** of §3 (p.8): for an $(\mathcal F_t)$-stopping time $\tau$ and an exit value $\theta$,
--   $$J(x,\tau;\theta)=E_x\Big[\int_0^\tau e^{-rs}D(X_s)\,ds+e^{-r\tau}\theta\Big],\qquad u(x;\theta)=\sup_{\tau\in\mathcal T(\mathcal F_t)}J(x,\tau;\theta). \tag{3.1–3.2}$$
--
--   Its threshold $\alpha(\theta)$ is the exit level of a firm whose rival never leaves; it is the building block of the equilibrium.
--
--   **Formalization Note** "Increasing" is non-strict (p.5). $\alpha$ is an argument tied down on $[\theta_L,\theta_U]$ by Assumption 3.1(ii); $\varphi$ is normalised at a reference point $c\in\mathcal I$, which changes no instance of Assumption 3.1. The infimum condition on $m$ is stated as the existence of $\kappa>\theta_U$ with $m\ge\kappa$ on $\mathcal I$. Stopping times take values in $[0,\infty]$ and $e^{-r\cdot\infty}=0$.
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, pp.5–6 (model, m, d, Assumption 2.3), §3 p.8 ((3.1), (3.2), (3.4), Assumption 3.1), Assumption 4.1 p.10

import Mathlib
import Definitions.Def_ExitGamePrivate_Diffusion

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ExitGamePrivate

/-- The data of the exit game of Kwon & Palczewski (arXiv:2210.01610v2, §2, pp.5–6, and
Assumption 4.1, p.10) on top of the state diffusion: the interest rate `r`, the duopoly profit
flow `D`, the monopoly profit flow `M`, the ends `θ_L ≤ θ_U` of the support of the exit values,
and the common cumulative distribution function `F` of the exit values `θ₁, θ₂`. -/
structure Model (Ω : Type*) [MeasurableSpace Ω] extends Diffusion Ω where
  r : ℝ
  D : ℝ → ℝ
  M : ℝ → ℝ
  θL : ℝ
  θU : ℝ
  F : ℝ → ℝ

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω)

/-- The expected discounted monopoly profit `m(x) = Eₓ[∫_0^∞ e^{-rs} M(X_s) ds]`, `x ∈ 𝓘`
(arXiv:2210.01610v2, p.6). -/
def m (x : ℝ) : ℝ :=
  ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (-(G.r * s)) * G.M (G.X x s ω)) ∂G.P

/-- The expected discounted duopoly profit `d(x) = Eₓ[∫_0^∞ e^{-rs} D(X_s) ds]`, `x ∈ 𝓘`
(arXiv:2210.01610v2, p.6). -/
def d (x : ℝ) : ℝ :=
  ∫ ω, (∫ s in Ioi (0 : ℝ), Real.exp (-(G.r * s)) * G.D (G.X x s ω)) ∂G.P

/-- The function `a_θ(x) = (θ − d(x))/φ(x)` of (3.4), p.8, with `φ = φ_c` the decreasing
fundamental solution normalised at the reference point `c` (see `Diffusion.phi`). -/
def a (c θ x : ℝ) : ℝ := (θ - G.d x) / G.phi G.r c x

/-- Assumption 2.3, p.6: "Functions D, M : 𝓘 → [0, ∞) are continuous, increasing and bounded, and
M > D. Furthermore, inf_{x∈𝓘} m(x) > θ_U, and the interest rate r > 0."

**Formalization Note** "Increasing" is non-strict (the paper's convention, p.5). The infimum
condition is stated as the existence of a constant `κ > θ_U` with `m ≥ κ` on `𝓘`, which is the
same condition and avoids a real `sInf`. -/
structure Assumption2_3 : Prop where
  D_nonneg : ∀ x ∈ G.I, 0 ≤ G.D x
  M_nonneg : ∀ x ∈ G.I, 0 ≤ G.M x
  D_cont : ContinuousOn G.D G.I
  M_cont : ContinuousOn G.M G.I
  D_mono : MonotoneOn G.D G.I
  M_mono : MonotoneOn G.M G.I
  D_bdd : ∃ C : ℝ, ∀ x ∈ G.I, G.D x ≤ C
  M_bdd : ∃ C : ℝ, ∀ x ∈ G.I, G.M x ≤ C
  M_gt_D : ∀ x ∈ G.I, G.D x < G.M x
  m_inf : ∃ κ : ℝ, G.θU < κ ∧ ∀ x ∈ G.I, κ ≤ G.m x
  r_pos : 0 < G.r

/-- A critical value `c(θ) ∈ 𝓘 ∪ {x_U}` of Assumption 3.1(i), p.8: `D(x) ≤ rθ` for `x < c(θ)` and
`D(x) > rθ` for `x > c(θ)`, `x ∈ 𝓘`. -/
def IsCritical (θ : ℝ) (cθ : EReal) : Prop :=
  G.xL < cθ ∧ cθ ≤ G.xU ∧
    ∀ x ∈ G.I, ((x : EReal) < cθ → G.D x ≤ G.r * θ) ∧ (cθ < (x : EReal) → G.r * θ < G.D x)

/-- Assumption 3.1, p.8, for the function `α`, with `φ = φ_c`:
(i) for each `θ ∈ [θ_L, θ_U]` there is a critical value `c(θ) ∈ 𝓘 ∪ {x_U}`;
(ii) for each `θ ∈ [θ_L, θ_U]`, `a_θ` attains a unique global maximum over `𝓘` at `α(θ) ∈ 𝓘`, is
differentiable at `α(θ)` and is increasing on `{x ∈ 𝓘 : x < α(θ)}`;
(iii) `α` is strictly increasing on `[θ_L, θ_U]`.

**Formalization Note** `α` is an argument, but (ii) pins it down on `[θ_L, θ_U]` as the unique
maximiser of `a_θ`, which is how the paper defines it; values of `α` outside `[θ_L, θ_U]` are
never used. Since `a_θ` depends on `φ` only through a positive factor, (ii)–(iii) do not depend on
the reference point `c`. -/
structure Assumption3_1 (c : ℝ) (α : ℝ → ℝ) : Prop where
  critical : ∀ θ ∈ Icc G.θL G.θU, ∃ cθ : EReal, G.IsCritical θ cθ
  α_mem : ∀ θ ∈ Icc G.θL G.θU, α θ ∈ G.I
  α_max : ∀ θ ∈ Icc G.θL G.θU, ∀ x ∈ G.I, x ≠ α θ → G.a c θ x < G.a c θ (α θ)
  α_diff : ∀ θ ∈ Icc G.θL G.θU, DifferentiableAt ℝ (G.a c θ) (α θ)
  α_incr : ∀ θ ∈ Icc G.θL G.θU, MonotoneOn (G.a c θ) (G.I ∩ Iio (α θ))
  α_strictMono : StrictMonoOn α (Icc G.θL G.θU)

/-- Assumption 4.1, p.10 (together with the support `[θ_L, θ_U]` of Assumption 2.2): the common
cumulative distribution function `F` of the exit values is continuous, strictly increasing on
`[θ_L, θ_U]`, vanishes on `(−∞, θ_L]` and equals `1` on `[θ_U, ∞)`.

**Formalization Note** These are exactly the properties of the CDF of a law on `ℝ` with support
`[θ_L, θ_U]` that is continuous and strictly increasing on its support; they force `θ_L < θ_U`.
That `F` is the CDF of `θ₁` and `θ₂` is stated with the type spaces (`TypeSpace.HasCDF`). -/
structure Assumption4_1 : Prop where
  cont : Continuous G.F
  strictMono : StrictMonoOn G.F (Icc G.θL G.θU)
  eq_zero : ∀ y ≤ G.θL, G.F y = 0
  eq_one : ∀ y, G.θU ≤ y → G.F y = 1

/-- The standing assumptions of §4 (p.10): the setting of §2 with Assumption 2.4, Assumption 2.3,
Assumption 3.1 (for `α`, with `φ` normalised at `c ∈ 𝓘`) and Assumption 4.1. -/
structure Standing (c : ℝ) (α : ℝ → ℝ) : Prop where
  regular : G.IsRegular
  c_mem : c ∈ G.I
  a23 : G.Assumption2_3
  a31 : G.Assumption3_1 c α
  a41 : G.Assumption4_1

/-- The single-player payoff (3.1), p.8: `J(x, τ; θ) = Eₓ[∫_0^τ e^{-rs} D(X_s) ds + e^{-rτ} θ]`
for a random time `τ ∈ [0, ∞]` on `Ω` (an `(Fₜ)`-stopping time in the paper); `e^{-r·∞} = 0`. -/
def Jsp (x : ℝ) (τ : Ω → WithTop ℝ≥0) (θ : ℝ) : ℝ :=
  ∫ ω, ((∫ s in window (τ ω), Real.exp (-(G.r * s)) * G.D (G.X x s ω)) +
    disc G.r (τ ω) * θ) ∂G.P

/-- The single-player value function (3.2), p.8: `u(x; θ) = sup_{τ ∈ 𝒯(Fₜ)} J(x, τ; θ)`.

**Formalization Note** The supremum runs over the `(Fₜ)`-stopping times with values in
`[0, ∞]`; the set is nonempty and, under Assumption 2.3, the payoffs are bounded, so the real
supremum is the paper's. -/
def u (x θ : ℝ) : ℝ :=
  ⨆ τ : {τ : Ω → WithTop ℝ≥0 // IsStoppingTime G.filt τ}, G.Jsp x τ.1 θ

end Model

end ExitGamePrivate


