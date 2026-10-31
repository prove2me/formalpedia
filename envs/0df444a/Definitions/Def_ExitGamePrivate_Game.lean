-- Prove2me | Definitions.Def_ExitGamePrivate_Game
-- name    : ExitGamePrivate_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:10.576277+00:00
-- url     : https://prove2.me/theorems/59dbd721-2827-4aab-9624-0c69f8db858c
-- title:
--   Private types, the product space (2.2), information filtrations $\mathcal F^i_t$, payoffs $J_1,J_2$, (2.3), and Nash equilibrium (Definition 2.6)
-- statement:
--   Each player $i=1,2$ has a private exit value $\theta_i$, a real random variable on a complete probability space $(\Omega^{\theta_i},\mathcal F^{\theta_i},P^{\theta_i})$. The game lives on the product
--   $$(\tilde\Omega,\tilde{\mathcal F},\tilde P)=(\Omega,\mathcal F,P)\otimes(\Omega^{\theta_1},\mathcal F^{\theta_1},P^{\theta_1})\otimes(\Omega^{\theta_2},\mathcal F^{\theta_2},P^{\theta_2}). \tag{2.2}$$
--   The public filtration $\tilde{\mathcal F}_t$ is the embedding of $\mathcal F_t$, and player $i$ observes $\mathcal F^i_t=\tilde{\mathcal F}_t\vee\sigma(\theta_i)$. Assumption 2.2 says that $\theta_i$ has support $[\theta_L,\theta_U]$; Assumption 4.1 that both have the CDF $F$.
--
--   For strategies $\tau_1,\tau_2$ (stopping times of $\mathcal F^1_t$, $\mathcal F^2_t$) the payoffs are (p.6)
--   $$J_1(x,\tau_1,\tau_2)=\tilde E_x\Big[\int_0^{\tau_1\wedge\tau_2}e^{-rt}D(X_t)\,dt+1_{\tau_1\le\tau_2}e^{-r\tau_1}\theta_1+1_{\tau_1>\tau_2}e^{-r\tau_2}m(X_{\tau_2})\Big],$$
--   and $J_2$ symmetrically. For a deterministic exit value $\gamma$, an $(\mathcal F_t)$-stopping time $\sigma$ and a random time $\tau$ on $\tilde\Omega$, (2.3) is
--   $$J(x,\sigma,\tau;\gamma)=\tilde E_x\Big[\int_0^{\sigma\wedge\tau}e^{-rt}D(X_t)\,dt+1_{\sigma\le\tau}e^{-r\sigma}\gamma+1_{\sigma>\tau}e^{-r\tau}m(X_\tau)\Big].$$
--
--   **Definition 2.6.** A profile $(\tau_1^*,\tau_2^*)\in\mathcal T(\mathcal F^1_t)\times\mathcal T(\mathcal F^2_t)$ is a **Nash equilibrium for $x$** if $J_1(x,\tau_1^*,\tau_2^*)\ge J_1(x,\tau_1,\tau_2^*)$ and $J_2(x,\tau_1^*,\tau_2^*)\ge J_2(x,\tau_1^*,\tau_2)$ for all $(\tau_1,\tau_2)\in\mathcal T(\mathcal F^1_t)\times\mathcal T(\mathcal F^2_t)$.
--
--   The module also records the class of type-indexed stopping times of Proposition 2.7: measurable maps $\hat\tau(\omega,\theta)$ whose sections $\hat\tau(\cdot,\theta)$, $\theta\in[\theta_L,\theta_U]$, are $(\mathcal F_t)$-stopping times.
--
--   **Formalization Note** Stopping times take values in $[0,\infty]$ with $e^{-r\cdot\infty}=0$; on $\{\tau_1>\tau_2\}$ the time $\tau_2$ is finite. The paper's "$\tilde P_x$-a.s." on the Nash inequalities is dropped because both sides are numbers. $\hat\tau$ is defined on $\Omega\times\mathbb R$ and read at $\max(\theta_L,\min(\theta_U,\theta_i))$, which is $\theta_i$ almost surely; this describes the same class as the paper's maps on $\Omega\times[\theta_L,\theta_U]$.
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, §2 pp.5–7: (2.2) p.5, information and payoffs p.6, Assumption 2.2 p.6, Definition 2.6 p.7, Proposition 2.7 p.7, (2.3) p.7

import Mathlib
import Definitions.Def_ExitGamePrivate_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ExitGamePrivate

/-- The private types: two probability spaces `(Ω^{θᵢ}, F^{θᵢ}, P^{θᵢ})` carrying the exit values
`θ₁, θ₂` (arXiv:2210.01610v2, p.5). `θᵢ` is a real random variable on `Θᵢ`. -/
structure TypeSpace (Θ₁ Θ₂ : Type*) [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] where
  Q₁ : Measure Θ₁
  Q₂ : Measure Θ₂
  θ₁ : Θ₁ → ℝ
  θ₂ : Θ₂ → ℝ
  measurable_θ₁ : Measurable θ₁
  measurable_θ₂ : Measurable θ₂

namespace TypeSpace

variable {Θ₁ Θ₂ : Type*} [MeasurableSpace Θ₁] [MeasurableSpace Θ₂] (T : TypeSpace Θ₁ Θ₂)

/-- The two type spaces are complete probability spaces (p.5). -/
structure IsComplete : Prop where
  prob₁ : IsProbabilityMeasure T.Q₁
  prob₂ : IsProbabilityMeasure T.Q₂
  complete₁ : T.Q₁.IsComplete
  complete₂ : T.Q₂.IsComplete

/-- Assumption 2.2, p.6: "Random variables θᵢ, i = 1, 2, have the support [θ_L, θ_U]": the
topological support of the law of each `θᵢ` is `[θ_L, θ_U]` (almost surely `θᵢ ∈ [θ_L, θ_U]`,
and every open neighbourhood of a point of `[θ_L, θ_U]` has positive probability). -/
structure HasSupport (θL θU : ℝ) : Prop where
  ae_mem₁ : ∀ᵐ ω ∂T.Q₁, T.θ₁ ω ∈ Icc θL θU
  ae_mem₂ : ∀ᵐ ω ∂T.Q₂, T.θ₂ ω ∈ Icc θL θU
  pos₁ : ∀ y ∈ Icc θL θU, ∀ ε : ℝ, 0 < ε → 0 < T.Q₁ {ω | T.θ₁ ω ∈ Ioo (y - ε) (y + ε)}
  pos₂ : ∀ y ∈ Icc θL θU, ∀ ε : ℝ, 0 < ε → 0 < T.Q₂ {ω | T.θ₂ ω ∈ Ioo (y - ε) (y + ε)}

/-- Assumption 4.1, p.10: `θ₁` and `θ₂` have the same cumulative distribution function `F`. -/
def HasCDF (F : ℝ → ℝ) : Prop :=
  (∀ y : ℝ, T.Q₁ {ω | T.θ₁ ω ≤ y} = ENNReal.ofReal (F y)) ∧
    ∀ y : ℝ, T.Q₂ {ω | T.θ₂ ω ≤ y} = ENNReal.ofReal (F y)

end TypeSpace

variable {Ω Θ₁ Θ₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ₁] [MeasurableSpace Θ₂]

/-- The product probability `P̃ = P ⊗ P^{θ₁} ⊗ P^{θ₂}` on `Ω̃ = Ω × Ω^{θ₁} × Ω^{θ₂}`, (2.2), p.5. -/
def Ptil (Dif : Diffusion Ω) (T : TypeSpace Θ₁ Θ₂) : Measure (Ω × Θ₁ × Θ₂) :=
  Dif.P.prod (T.Q₁.prod T.Q₂)

/-- The embedding `F̃ₜ = σ({A × Ω^{θ₁} × Ω^{θ₂} : A ∈ Fₜ})` of the filtration `(Fₜ)` into `Ω̃`
(p.5), indexed by `t ∈ ℝ≥0`. -/
def filtTil (Dif : Diffusion Ω) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Θ₁ × Θ₂)) where
  seq t := (Dif.filt t).comap Prod.fst
  mono' _ _ h := MeasurableSpace.comap_mono (Dif.filt.mono h)
  le' t := (MeasurableSpace.comap_mono (Dif.filt.le t)).trans measurable_fst.comap_le

/-- The information filtration of player 1, `F¹ₜ = F̃ₜ ∨ σ(θ₁)` (p.6). -/
def filt₁ (Dif : Diffusion Ω) (T : TypeSpace Θ₁ Θ₂) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Θ₁ × Θ₂)) where
  seq t := (filtTil (Θ₁ := Θ₁) (Θ₂ := Θ₂) Dif t) ⊔
    (inferInstance : MeasurableSpace ℝ).comap (fun ω : Ω × Θ₁ × Θ₂ => T.θ₁ ω.2.1)
  mono' _ _ h := sup_le_sup_right ((filtTil Dif).mono h) _
  le' t := sup_le ((filtTil Dif).le t)
    (T.measurable_θ₁.comp (measurable_fst.comp measurable_snd)).comap_le

/-- The information filtration of player 2, `F²ₜ = F̃ₜ ∨ σ(θ₂)` (p.6). -/
def filt₂ (Dif : Diffusion Ω) (T : TypeSpace Θ₁ Θ₂) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Θ₁ × Θ₂)) where
  seq t := (filtTil (Θ₁ := Θ₁) (Θ₂ := Θ₂) Dif t) ⊔
    (inferInstance : MeasurableSpace ℝ).comap (fun ω : Ω × Θ₁ × Θ₂ => T.θ₂ ω.2.2)
  mono' _ _ h := sup_le_sup_right ((filtTil Dif).mono h) _
  le' t := sup_le ((filtTil Dif).le t)
    (T.measurable_θ₂.comp (measurable_snd.comp measurable_snd)).comap_le

namespace Model

variable (G : Model Ω)

/-- The realised payoff of a player who stops at `τa`, when the opponent stops at `τb`, with exit
value `γ`, along the path `ω` of the diffusion started at `x`:
`∫_0^{τa∧τb} e^{-rt} D(Xₜ) dt + 1_{τa ≤ τb} e^{-rτa} γ + 1_{τa > τb} e^{-rτb} m(X_{τb})`.
This is the integrand of `J₁, J₂` (p.6) and of (2.3) (p.7).

**Formalization Note** On `{τa > τb}` the time `τb` is finite, so `X_{τb}` is evaluated at the
real time `τb`; on `{τa = τb = ∞}` the exit term is `1 · e^{-r·∞} · γ = 0`. -/
def payoff (x : ℝ) (ω : Ω) (τa τb : WithTop ℝ≥0) (γ : ℝ) : ℝ :=
  (∫ t in window (min τa τb), Real.exp (-(G.r * t)) * G.D (G.X x t ω)) +
    (if τa ≤ τb then disc G.r τa * γ else 0) +
    (if τb < τa then disc G.r τb * G.m (G.X x ((τb.untopD 0 : ℝ≥0) : ℝ) ω) else 0)

/-- The payoff of Player 1 (p.6):
`J₁(x, τ₁, τ₂) = Ẽₓ[∫_0^{τ₁∧τ₂} e^{-rt} D(Xₜ) dt + 1_{τ₁≤τ₂} e^{-rτ₁} θ₁ + 1_{τ₁>τ₂} e^{-rτ₂} m(X_{τ₂})]`. -/
def J₁ (T : TypeSpace Θ₁ Θ₂) (x : ℝ) (τ₁ τ₂ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0) : ℝ :=
  ∫ ω, G.payoff x ω.1 (τ₁ ω) (τ₂ ω) (T.θ₁ ω.2.1) ∂(Ptil G.toDiffusion T)

/-- The payoff of Player 2 (p.6):
`J₂(x, τ₁, τ₂) = Ẽₓ[∫_0^{τ₁∧τ₂} e^{-rt} D(Xₜ) dt + 1_{τ₂≤τ₁} e^{-rτ₂} θ₂ + 1_{τ₂>τ₁} e^{-rτ₁} m(X_{τ₁})]`. -/
def J₂ (T : TypeSpace Θ₁ Θ₂) (x : ℝ) (τ₁ τ₂ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0) : ℝ :=
  ∫ ω, G.payoff x ω.1 (τ₂ ω) (τ₁ ω) (T.θ₂ ω.2.2) ∂(Ptil G.toDiffusion T)

/-- The payoff functional (2.3), p.7, for a deterministic exit value `γ`, an `(Fₜ)`-stopping time
`σ` on `Ω` (lifted to `Ω̃`) and a random time `τ` on `Ω̃`:
`J(x, σ, τ; γ) = Ẽₓ[∫_0^{σ∧τ} e^{-rt} D(Xₜ) dt + 1_{σ≤τ} e^{-rσ} γ + 1_{σ>τ} e^{-rτ} m(X_τ)]`. -/
def Jgam (T : TypeSpace Θ₁ Θ₂) (x : ℝ) (σ : Ω → WithTop ℝ≥0)
    (τ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0) (γ : ℝ) : ℝ :=
  ∫ ω, G.payoff x ω.1 (σ ω.1) (τ ω) γ ∂(Ptil G.toDiffusion T)

/-- Definition 2.6, p.7: `(τ₁*, τ₂*) ∈ 𝒯(F¹ₜ) × 𝒯(F²ₜ)` is a Nash equilibrium for `x` if for any
`(τ₁, τ₂) ∈ 𝒯(F¹ₜ) × 𝒯(F²ₜ)`, `J₂(x, τ₁*, τ₂*) ≥ J₂(x, τ₁*, τ₂)` and
`J₁(x, τ₁*, τ₂*) ≥ J₁(x, τ₁, τ₂*)`.

**Formalization Note** Stopping times take values in `[0, ∞]` (`WithTop ℝ≥0`). The paper's
"P̃ₓ-a.s." attached to these inequalities between numbers is dropped: both sides are
expectations, i.e. real numbers. -/
def IsNash (T : TypeSpace Θ₁ Θ₂) (x : ℝ) (τ₁ τ₂ : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0) : Prop :=
  IsStoppingTime (filt₁ G.toDiffusion T) τ₁ ∧ IsStoppingTime (filt₂ G.toDiffusion T) τ₂ ∧
    (∀ τ₁' : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0, IsStoppingTime (filt₁ G.toDiffusion T) τ₁' →
      G.J₁ T x τ₁' τ₂ ≤ G.J₁ T x τ₁ τ₂) ∧
    (∀ τ₂' : Ω × Θ₁ × Θ₂ → WithTop ℝ≥0, IsStoppingTime (filt₂ G.toDiffusion T) τ₂' →
      G.J₂ T x τ₁ τ₂' ≤ G.J₂ T x τ₁ τ₂)

end Model

/-- `clampθ θL θU y = max θL (min θU y)`: the value of `y` moved into `[θ_L, θ_U]`. It equals `y`
whenever `y ∈ [θ_L, θ_U]`, in particular almost surely for `y = θᵢ` under Assumption 2.2; it is
used so that `τ̂(·, θᵢ)` only reads `τ̂(·, θ)` at `θ ∈ [θ_L, θ_U]`, the domain of `τ̂` in
Proposition 2.7 (p.7). -/
def clampθ (θL θU y : ℝ) : ℝ := max θL (min θU y)

/-- A type-indexed family of `(Fₜ)`-stopping times as in Proposition 2.7, p.7: `τ̂ : Ω × ℝ → [0, ∞]`
is `F ⊗ 𝓑`-measurable and `τ̂(·, θ)` is an `(Fₜ)`-stopping time for each `θ ∈ [θ_L, θ_U]`.

**Formalization Note** The paper's `τ̂` is defined on `Ω × [θ_L, θ_U]`; every such map extends to
`Ω × ℝ` (for instance through `clampθ`), so taking `τ̂` on `Ω × ℝ` and asking the stopping-time
property only on `[θ_L, θ_U]` describes the same class. Values in `[0, ∞]` rather than `[0, ∞)`:
see the theorems using it. -/
def IsTypedStopping (Dif : Diffusion Ω) (θL θU : ℝ) (τh : Ω → ℝ → WithTop ℝ≥0) : Prop :=
  Measurable (Function.uncurry τh) ∧ ∀ θ ∈ Icc θL θU, IsStoppingTime Dif.filt (fun ω => τh ω θ)

end ExitGamePrivate


