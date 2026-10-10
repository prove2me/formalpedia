-- Prove2me | Definitions.Def_MasterVisc_MKV_Control
-- name    : MasterVisc_MKV_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:34:08.045497+00:00
-- url     : https://prove2.me/theorems/8e8715d8-c8b2-410c-94d7-d82f63e91732
-- title:
--   §3.2 and §5 — Assumption 5.1, controls 𝒜_t (5.3) and 𝒜⁰_t (5.12), the controlled law (3.18), J, V, V₀ (3.20), the HJB generator (3.22)
-- statement:
--   This file sets up the closed-loop McKean–Vlasov control problem of §3.2 and §5.
--
--   Let $A$ be the control set, and let $b(t,\omega,\mu,a)\in\mathbb R^d$, $\sigma(t,\omega,\mu,a)\in\mathbb R^{d\times d}$, $f(t,\omega,\mu,a)\in\mathbb R$ and $g(\omega,\mu)\in\mathbb R$ be the coefficients.
--
--   1. **Modulus.** $\rho:\mathbb R\to\mathbb R$ is a modulus of continuity function if $\rho\ge0$ on $[0,\infty)$, $\rho(0)=0$, $\rho$ is nondecreasing on $[0,\infty)$ and $\rho(r)\to0$ as $r\downarrow0$.
--   2. **Assumption 5.1.** $b,\sigma,f$ are jointly measurable in $(t,\omega,\mu,a)$ and $\mathbb F$-adapted in $\omega$ and $\mu$, i.e. $\varphi(t,\omega,\mu,a)=\varphi(t,\omega_{t\wedge\cdot},\mu_{[0,t]},a)$; $g$ is jointly measurable. Moreover: (i) $|b|,|\sigma|\le C_0$, $b,\sigma$ are continuous in $a$, and
--   $$|(b,\sigma)(t,\omega,\mu,a)-(b,\sigma)(t,\omega',\mu',a)|\le L_0\big[\|\omega_{t\wedge\cdot}-\omega'_{t\wedge\cdot}\|+\mathcal W_2(\mu_{[0,t]},\mu'_{[0,t]})\big];$$
--   (ii) $|f(t,0,\delta_{\{0\}},a)|\le C_0$, $f$ is continuous in $a$, $|f(t,\omega,\mu,a)-f(t,\omega',\mu',a)|\le\rho_0\big(\|\omega_{t\wedge\cdot}-\omega'_{t\wedge\cdot}\|+\mathcal W_2((t,\mu),(t,\mu'))\big)$ and $|g(\omega,\mu)-g(\omega',\mu')|\le\rho_0\big(\|\omega-\omega'\|+\mathcal W_2((T,\mu),(T,\mu'))\big)$; (iii) for $\varphi=b,\sigma,f$ and $t<s$, $|\varphi(s,\omega_{t\wedge\cdot},\mu_{[0,t]},a)-\varphi(t,\omega,\mu,a)|\le C\big[1+\|\omega_{t\wedge\cdot}\|+\mathcal W_2(\mu_{[0,t]},\delta_{\{0\}})\big]\rho_0(s-t)$; (iv) $\sigma\sigma^\top$ is positive definite.
--   3. **Controls.** $\alpha\in\mathcal A_t$ (5.3) if for some partition $t=t_0<\dots<t_n=T$, $\alpha_s=\sum_{i<n}h_i\mathbf 1_{[t_i,t_{i+1})}(s)$ with $h_i:\Omega\to A$ $\mathcal F_{t_i}$-measurable. $\alpha\in\mathcal A^0_t$ (5.12) if moreover, for some $0\le s_1<\dots<s_m\le t$, each $h_i=h_i(X_{s_1},\dots,X_{s_m},X_{[t,t_i]})$ for a measurable function.
--   4. **Controlled law (3.18).** $\mathbb P^{t,\mu,\alpha}\in\mathcal P_2$ with $\mathbb P^{t,\mu,\alpha}_{[0,t]}=\mu_{[0,t]}$ such that, for $s\in[t,T]$ and a Brownian motion $B^\alpha$,
--   $$X_s=X_t+\int_t^s b\big(r,X_{r\wedge\cdot},\mathbb P^{t,\mu,\alpha}_{[0,r]},\alpha_r(X_{r\wedge\cdot})\big)dr+\int_t^s\sigma\big(r,X_{r\wedge\cdot},\mathbb P^{t,\mu,\alpha}_{[0,r]},\alpha_r(X_{r\wedge\cdot})\big)dB^\alpha_r.$$
--   5. **Values (3.20), (5.12).** $J(t,\mu,\alpha)=\mathbb E^{\mathbb P}\big[g(X,\mathbb P)+\int_t^Tf(s,X,\mathbb P,\alpha_s)\,ds\big]$ with $\mathbb P=\mathbb P^{t,\mu,\alpha}$; $V(t,\mu)=\sup_{\alpha\in\mathcal A_t}J(t,\mu,\alpha)$ and $V_0(t,\mu)=\sup_{\alpha\in\mathcal A^0_t}J(t,\mu,\alpha)$.
--   6. **HJB generator (3.22).** $G(t,\mu,y,Z,\Gamma)=\mathbb E^\mu\big[\sup_{a\in A}G_2(t,\mu,X,Z(X),\Gamma(X),a)\big]$, where
--   $$G_2(t,\mu,\omega,z,\gamma,a)=\tfrac12\gamma:\sigma\sigma^\top(t,\omega,\mu,a)+z\cdot b(t,\omega,\mu,a)+f(t,\omega,\mu,a).$$
--
--   **Formalization Note.** $|\sigma|$ is the Frobenius norm, and the joint bound on $(b,\sigma)$ in (i) is stated as two bounds with the same $L_0$. $\delta_{\{0\}}$ is the Dirac mass at the zero path. "$\mathbb F$-progressively measurable in all variables" is encoded as joint measurability (Giry $\sigma$-algebra on laws) plus adaptedness in $\omega$ and $\mu$, which the page names as the consequence used. All conditions are required on the paper's domain $t\le T$, $\mu\in\mathcal P_2$. The control set $A$ is left as a parameter here; the statements take $A$ nonempty Polish with its Borel $\sigma$-algebra (the paper says "some appropriate set $A$"). (3.18) is encoded in the weak sense: $\mathbb P^{t,\mu,\alpha}$ has a semimartingale representation from $t$ whose drift and diffusion are the controlled coefficients along the represented path on $[t,T)$; the Brownian motion lives on the representation's space. $\alpha_T$ is not constrained by (5.3), and the single time $T$ is Lebesgue-null. $V$ and $V_0$ are suprema in the extended reals over the admissible pairs $(\alpha,\mathbb P^{t,\mu,\alpha})$, so an empty admissible set gives $-\infty$, not a default value. Under Assumption 5.1 the real supremum over $a$ in $G$ is finite ($b,\sigma$ bounded, $f$ bounded in $a$ by (ii)) and measurable in $\omega$ ($A$ separable, continuity in $a$), and $J$ is an integral of an integrable function.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), (3.18)–(3.20) pp. 951–952, (3.22) p. 952, Assumption 5.1 p. 968, (5.3) p. 970, (5.12) p. 974

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

open EthierKurtz

variable {d : ℕ} {T : ℝ≥0}

/-- A modulus of continuity function: `ρ ≥ 0` on `[0, ∞)`, `ρ(0) = 0`, `ρ` nondecreasing on
`[0, ∞)` and `ρ(r) → 0` as `r ↓ 0`. -/
def IsModulus (ρ : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → 0 ≤ ρ r) ∧ ρ 0 = 0 ∧ MonotoneOn ρ (Set.Ici 0) ∧ Tendsto ρ (𝓝[≥] 0) (𝓝 0)

/-- The window `X_{[t,u]}` as a path: `r ↦ ω((t ∨ r) ∧ u)` (clamped to `[0, T]`). -/
def window (t u : ℝ≥0) (ω : MasterVisc.Comparison.Path d T) : MasterVisc.Comparison.Path d T :=
  ω.comp ⟨fun r => ⟨min (min (max r.1 t) u) T, zero_le, min_le_right _ _⟩,
    Continuous.subtype_mk
      (((continuous_subtype_val.max continuous_const).min continuous_const).min
        continuous_const) _⟩

section Control

variable {A : Type} [TopologicalSpace A] [MeasurableSpace A]

/-- Assumption 5.1 (p. 968) on the coefficients `b, σ, f : [0, T] × Ω × 𝒫₂ × A → ℝ^d, ℝ^{d×d}, ℝ`
and `g : Ω × 𝒫₂ → ℝ`, with constants `C₀`, `L₀`, `C` and modulus `ρ₀`:
measurability (jointly measurable and `𝔽`-adapted in `ω` and `μ`), (i) boundedness by `C₀`,
continuity in `a` and Lipschitz continuity in `(ω, μ)` of `b, σ`; (ii) `|f(t, 0, δ_{0}, a)| ≤ C₀`,
continuity of `f` in `a`, and uniform continuity of `f, g` in `(ω, μ)` with modulus `ρ₀`;
(iii) local uniform continuity in `t`; (iv) `σσ^⊤` positive definite. Here `|σ|` is the Frobenius
norm and `δ_{0}` is the Dirac mass at the zero path. -/
def Assumption51 (C₀ L₀ : ℝ) (ρ₀ : ℝ → ℝ) (C : ℝ)
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  -- measurability and adaptedness
  (Measurable (fun p : ℝ≥0 × MasterVisc.Comparison.Path d T × Measure (MasterVisc.Comparison.Path d T) × A =>
    b p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧
  (∀ i j, Measurable (fun p : ℝ≥0 × MasterVisc.Comparison.Path d T × Measure (MasterVisc.Comparison.Path d T) × A =>
    σ p.1 p.2.1 p.2.2.1 p.2.2.2 i j)) ∧
  (Measurable (fun p : ℝ≥0 × MasterVisc.Comparison.Path d T × Measure (MasterVisc.Comparison.Path d T) × A =>
    f p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧
  (Measurable (fun p : MasterVisc.Comparison.Path d T × Measure (MasterVisc.Comparison.Path d T) => g p.1 p.2)) ∧
  (∀ t ω μ a, t ≤ T → MasterVisc.Comparison.IsP2 μ →
    b t ω μ a = b t (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a ∧
    σ t ω μ a = σ t (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a ∧
    f t ω μ a = f t (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a) ∧
  -- (i)
  (∀ t ω μ a, t ≤ T → MasterVisc.Comparison.IsP2 μ →
    ‖b t ω μ a‖ ≤ C₀ ∧ Real.sqrt (MasterVisc.Comparison.frob2 (σ t ω μ a)) ≤ C₀) ∧
  (∀ t ω μ, t ≤ T → MasterVisc.Comparison.IsP2 μ → Continuous (b t ω μ) ∧ Continuous (σ t ω μ)) ∧
  (∀ t ω ω' μ μ' a, t ≤ T → MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 μ' →
    ‖b t ω μ a - b t ω' μ' a‖ ≤
        L₀ * (‖MasterVisc.Comparison.stopAt t ω - MasterVisc.Comparison.stopAt t ω'‖ + W2 (MasterVisc.Comparison.restr t μ) (MasterVisc.Comparison.restr t μ')) ∧
    Real.sqrt (MasterVisc.Comparison.frob2 (σ t ω μ a - σ t ω' μ' a)) ≤
        L₀ * (‖MasterVisc.Comparison.stopAt t ω - MasterVisc.Comparison.stopAt t ω'‖ + W2 (MasterVisc.Comparison.restr t μ) (MasterVisc.Comparison.restr t μ'))) ∧
  -- (ii)
  (∀ t a, t ≤ T → |f t 0 (Measure.dirac 0) a| ≤ C₀) ∧
  (∀ t ω μ, t ≤ T → MasterVisc.Comparison.IsP2 μ → Continuous (f t ω μ)) ∧
  (∀ t ω ω' μ μ' a, t ≤ T → MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 μ' →
    |f t ω μ a - f t ω' μ' a| ≤ ρ₀ (‖MasterVisc.Comparison.stopAt t ω - MasterVisc.Comparison.stopAt t ω'‖ + MasterVisc.Comparison.W2Θ t μ t μ')) ∧
  (∀ ω ω' μ μ', MasterVisc.Comparison.IsP2 μ → MasterVisc.Comparison.IsP2 μ' →
    |g ω μ - g ω' μ'| ≤ ρ₀ (‖ω - ω'‖ + MasterVisc.Comparison.W2Θ T μ T μ')) ∧
  -- (iii)
  0 ≤ C ∧
  (∀ t s ω μ a, t < s → s ≤ T → MasterVisc.Comparison.IsP2 μ →
    ‖b s (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a - b t ω μ a‖ ≤
        C * (1 + ‖MasterVisc.Comparison.stopAt t ω‖ + W2 (MasterVisc.Comparison.restr t μ) (Measure.dirac 0)) * ρ₀ ((s : ℝ) - t) ∧
    Real.sqrt (MasterVisc.Comparison.frob2 (σ s (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a - σ t ω μ a)) ≤
        C * (1 + ‖MasterVisc.Comparison.stopAt t ω‖ + W2 (MasterVisc.Comparison.restr t μ) (Measure.dirac 0)) * ρ₀ ((s : ℝ) - t) ∧
    |f s (MasterVisc.Comparison.stopAt t ω) (MasterVisc.Comparison.restr t μ) a - f t ω μ a| ≤
        C * (1 + ‖MasterVisc.Comparison.stopAt t ω‖ + W2 (MasterVisc.Comparison.restr t μ) (Measure.dirac 0)) * ρ₀ ((s : ℝ) - t)) ∧
  -- (iv)
  (∀ t ω μ a, t ≤ T → MasterVisc.Comparison.IsP2 μ → (σ t ω μ a * (σ t ω μ a).transpose).PosDef)

/-- `α ∈ 𝒜_t` (5.3, p. 970): a piecewise constant control
`α_s = ∑_{i<n} h_i 1_{[t_i, t_{i+1})}(s)` for a partition `t = t₀ < ⋯ < tₙ = T`, with each
`h_i : Ω → A` being `F_{t_i}`-measurable. -/
def IsPWControl (t : ℝ≥0) (α : ℝ≥0 → MasterVisc.Comparison.Path d T → A) : Prop :=
  ∃ n : ℕ, ∃ τ : Fin (n + 1) → ℝ≥0, StrictMono τ ∧ τ 0 = t ∧ τ (Fin.last n) = T ∧
    ∃ h : Fin n → MasterVisc.Comparison.Path d T → A,
      (∀ i, Measurable[MasterVisc.Comparison.filt (τ i.castSucc)] (h i)) ∧
      ∀ i s ω, τ i.castSucc ≤ s → s < τ i.succ → α s ω = h i ω

/-- `α ∈ 𝒜⁰_t` (5.12, p. 974): `α ∈ 𝒜_t` whose pieces depend on `X_{[0,t]}` only discretely,
`h_i = h_i(X_{s₁}, …, X_{s_m}, X_{[t, t_i]})` for some `0 ≤ s₁ < ⋯ < s_m ≤ t`. -/
def IsDiscControl (t : ℝ≥0) (α : ℝ≥0 → MasterVisc.Comparison.Path d T → A) : Prop :=
  ∃ n : ℕ, ∃ τ : Fin (n + 1) → ℝ≥0, StrictMono τ ∧ τ 0 = t ∧ τ (Fin.last n) = T ∧
    ∃ h : Fin n → MasterVisc.Comparison.Path d T → A,
      (∀ i, Measurable[MasterVisc.Comparison.filt (τ i.castSucc)] (h i)) ∧
      (∀ i s ω, τ i.castSucc ≤ s → s < τ i.succ → α s ω = h i ω) ∧
      ∃ m : ℕ, ∃ sp : Fin m → ℝ≥0, StrictMono sp ∧ (∀ j, sp j ≤ t) ∧
        ∃ k : Fin n → (Fin m → SDEState d) × MasterVisc.Comparison.Path d T → A,
          (∀ i, Measurable (k i)) ∧
          ∀ i ω, h i ω = k i (fun j => MasterVisc.Comparison.evalAt (sp j) ω, window t (τ i.castSucc) ω)

/-- `P = ℙ^{t,μ,α}` (3.18): `P ∈ 𝒫₂`, `P_{[0,t]} = μ_{[0,t]}`, and on `[t, T]` the canonical process
solves `dX_s = b(s, X_{s∧·}, P_{[0,s]}, α_s(X_{s∧·})) ds + σ(…) dB^α_s` for a Brownian motion
`B^α`, in the weak sense: `P` has a semimartingale representation from `t` whose drift and
diffusion are the controlled coefficients evaluated along the represented path on `[t, T)`.
(The value `α_T` is not constrained by (5.3); the single time `T` is Lebesgue-null in (3.18).) -/
def IsControlledLaw
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) (α : ℝ≥0 → MasterVisc.Comparison.Path d T → A) (P : Measure (MasterVisc.Comparison.Path d T)) :
    Prop :=
  MasterVisc.Comparison.IsP2 P ∧ MasterVisc.Comparison.restr t P = MasterVisc.Comparison.restr t μ ∧
    ∃ R : Rep d T, IsRepFrom t P R ∧
      ∀ r ω, t ≤ r → r < T →
        R.b r ω = b r (MasterVisc.Comparison.stopAt r (R.Y ω)) (MasterVisc.Comparison.restr r P) (α r (MasterVisc.Comparison.stopAt r (R.Y ω))) ∧
        R.σ r ω = σ r (MasterVisc.Comparison.stopAt r (R.Y ω)) (MasterVisc.Comparison.restr r P) (α r (MasterVisc.Comparison.stopAt r (R.Y ω)))

/-- The reward `J(t, μ, α) = 𝔼^P[g(X, P) + ∫_t^T f(s, X, P, α_s) ds]` of (3.20), for
`P = ℙ^{t,μ,α}`. -/
noncomputable def Jval
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (t : ℝ≥0) (α : ℝ≥0 → MasterVisc.Comparison.Path d T → A) (P : Measure (MasterVisc.Comparison.Path d T)) : ℝ :=
  ∫ ω, (g ω P + ∫ s in (t : ℝ)..(T : ℝ), f s.toNNReal ω P (α s.toNNReal ω)) ∂P

/-- Admissible pairs `(α, ℙ^{t,μ,α})` with `α ∈ 𝒜_t` of (5.3). -/
def AdmPair
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) : Type :=
  {p : (ℝ≥0 → MasterVisc.Comparison.Path d T → A) × Measure (MasterVisc.Comparison.Path d T) //
    IsPWControl t p.1 ∧ IsControlledLaw b σ t μ p.1 p.2}

/-- Admissible pairs `(α, ℙ^{t,μ,α})` with `α ∈ 𝒜⁰_t` of (5.12). -/
def AdmPair0
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) : Type :=
  {p : (ℝ≥0 → MasterVisc.Comparison.Path d T → A) × Measure (MasterVisc.Comparison.Path d T) //
    IsDiscControl t p.1 ∧ IsControlledLaw b σ t μ p.1 p.2}

/-- The value function (3.20) with the admissible set (5.3):
`V(t, μ) = sup_{α ∈ 𝒜_t} J(t, μ, α)`, in `EReal`. -/
noncomputable def Vval
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) : EReal :=
  ⨆ p : AdmPair b σ t μ, ((Jval f g t p.1.1 p.1.2 : ℝ) : EReal)

/-- The value function with discretely observing controls (5.12):
`V₀(t, μ) = sup_{α ∈ 𝒜⁰_t} J(t, μ, α)`, in `EReal`. -/
noncomputable def V0val
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ)
    (g : MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → ℝ)
    (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) : EReal :=
  ⨆ p : AdmPair0 b σ t μ, ((Jval f g t p.1.1 p.1.2 : ℝ) : EReal)

/-- The HJB generator of (3.22):
`G(t, μ, y, Z, Γ) = 𝔼^μ[sup_{a ∈ A} G₂(t, μ, X, Z(X), Γ(X), a)]` with
`G₂(t, μ, ω, z, γ, a) = ½ γ : σσ^⊤(t, ω, μ, a) + z · b(t, ω, μ, a) + f(t, ω, μ, a)`.
It does not depend on `y`. -/
noncomputable def G322
    (b : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → SDEState d)
    (σ : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ≥0 → MasterVisc.Comparison.Path d T → Measure (MasterVisc.Comparison.Path d T) → A → ℝ) : MasterVisc.Comparison.Gen d T :=
  fun t μ _y Z Γ => ∫ ω, (⨆ a : A,
    (MasterVisc.Comparison.fdot (Γ ω) (σ t ω μ a * (σ t ω μ a).transpose) / 2 + inner ℝ (Z ω) (b t ω μ a) +
      f t ω μ a)) ∂μ

end Control

end MasterVisc.MKV


