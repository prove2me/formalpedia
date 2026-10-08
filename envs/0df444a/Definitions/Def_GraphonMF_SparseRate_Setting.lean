-- Prove2me | Definitions.Def_GraphonMF_SparseRate_Setting
-- name    : GraphonMF_SparseRate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:04.991546+00:00
-- url     : https://prove2.me/theorems/f52bd853-2f8a-498e-8e0e-15af57a378bd
-- title:
--   §1.2, §2, §4, §7.1, pp. 3590–3611 — graphons, 𝒞_d, W₂, the class ℳ, the continuum noise, the systems (4.1) and (4.2), Conditions 2.3, 4.1, 4.3, the terms R^{n,2}_s, R^{n,4}_s of (7.2)
-- statement:
--   This file fixes the objects of the not-so-dense graphon particle system of Bayraktar, Chakraborty and Wu, in the setting of their Theorem 4.2.
--
--   **Labels and graphons.** Let $I=[0,1]$ with Lebesgue measure. Particle $i\in\{1,\dots,n\}$ carries the label $i/n\in I$; the step point of $u\in I$ is $\lceil nu\rceil/n$. A **graphon** is a jointly measurable symmetric function $G:I\times I\to[0,1]$. The cut norm $\|W\|_\square=\sup_{S,T}\left|\int_{S\times T}W(u,v)\,du\,dv\right|$ (sup over Borel $S,T\subseteq I$) and step graphons ($G_n(u,v)=G_n(\lceil nu\rceil/n,\lceil nv\rceil/n)$) are also defined, for use by the series.
--
--   **Paths and laws.** $\mathcal C_d=C([0,T]:\mathbb R^d)$ with $\|x\|_{*,t}=\sup_{0\le s\le t}|x_s|$; $\|x\|_{*,T}$ is the norm of $\mathcal C_d$. $W_2$ on $\mathcal P(\mathbb R^d)$ and $W_{2,T}$ on $\mathcal P(\mathcal C_d)$ are the Wasserstein-2 distances (2.3)–(2.4), with values in $[0,\infty]$. The class $\mathcal M$ consists of measurable families $(\nu_u)_{u\in I}$ of probability measures on $\mathcal C_d$ with $\sup_u\int\|x\|_{*,T}^2\,\nu_u(dx)<\infty$.
--
--   **Noise.** One probability space carries initial states $X_u(0)\sim\mu_u(0)$ and standard $d$-dimensional Brownian motions $B_u$, $u\in I$, the family $\{X_u(0)\}_{u\in I}\cup\{B_u\}_{u\in I}$ being mutually independent. $X_u$ is adapted to $\sigma(X_u(0),B_u(s):s\le t)$; the $n$-particle system to $\sigma(\xi^n,X_{j/n}(0),B_{j/n}(s):j\le n,\ s\le t)$.
--
--   **Conditions.**
--   1. *Condition 2.3*: a finite cover $\{I_i\}_{i=1}^N$ of $I$ by intervals and $\kappa>0$ with $W_2(\mu_{u_1}(0),\mu_{u_2}(0))\le\kappa|u_1-u_2|$ on each $I_i$ and $|G(u_1,v_1)-G(u_2,v_2)|\le\kappa(|u_1-u_2|+|v_1-v_2|)$ on each $I_i\times I_j$.
--   2. *Condition 4.1*: (a) $u\mapsto\mu_u(0)$ measurable with $\sup_u\mathbb E|X_u(0)|^2<\infty$; (b) $b$ bounded and Lipschitz; (c) $\sigma$ bounded, Lipschitz, with $\sigma(x)$ invertible and $\sup_x|\sigma(x)^{-1}|<\infty$; (d) $\beta_n\in(0,1]$ and $n\beta_n\to\infty$.
--   3. *Condition 4.3*: for each $n$, $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(\beta_nG(i/n,j/n))$, independent for $1\le i\le j\le n$ and independent of $\{B_u,X_u(0):u\in I\}$.
--
--   **Systems.** A solution of the limit system (4.2) is a family $X=(X_u)_{u\in I}$ with continuous paths, path laws in $\mathcal M$, and
--   $$X_u(t)=X_u(0)+\int_0^t\!\int_I\!\int_{\mathbb R^d}b(X_u(s),x)G(u,v)\,\mu_{v,s}(dx)\,dv\,ds+\int_0^t\sigma(X_u(s))\,dB_u(s),\qquad \mu_{v,s}=\mathcal L(X_v(s)).$$
--   A solution of the not-so-dense system (4.1) is $(X^n_i)_{i\le n}$ with continuous paths and
--   $$X^n_i(t)=X_{i/n}(0)+\int_0^t\frac{1}{n\beta_n}\sum_{j=1}^n\xi^n_{ij}\,b(X^n_i(s),X^n_j(s))\,ds+\int_0^t\sigma(X^n_i(s))\,dB_{i/n}(s).$$
--
--   **Error terms of (7.2)**, with $G$ in place of $G_n$:
--   $$R^{n,2}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\frac{\xi^n_{ij}}{\beta_n}\big(b(X_{i/n}(s),X^n_j(s))-b(X_{i/n}(s),X_{j/n}(s))\big)\Big|^2,$$
--   $$R^{n,4}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\int b(X_{i/n}(s),x)G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)-\int_I\!\int b(X_{i/n}(s),x)G(\tfrac in,v)\,\mu_{v,s}(dx)\,dv\Big|^2.$$
--
--   These are the shared objects of every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with the sup norm, and matrix bounds are entrywise; every statement of the paper is invariant under the choice of norm, since its constants are existential. Lean's `i : Fin n` is the paper's $i+1$, with label $(i+1)/n$. Time is `ℝ≥0`; Itô integrals, Brownian motions and Itô processes are those of the published `Peng1990.SMP.Stochastic` (uncompleted natural filtrations; the independence assumptions make each driving $B$ a Brownian motion for them). An SDE with random initial value $X(0)$ is encoded as an Itô process for $X-X(0)$ started at $0$. Measurability of $u\mapsto\nu_u$ is for the Giry σ-algebra on measures, which on the Polish space $\mathcal C_d$ is the Borel σ-algebra of weak convergence. Membership of the path laws in $\mathcal M$ and AE-measurability of the path maps are part of the solution concept (Proposition 2.1 gives both), so that the drift integrals and laws are meaningful. Expectations of nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$. The intervals of Condition 2.3 are order-connected subsets of $I$. Condition 4.1(d) is required for $n\ge1$. "Bounded inverse $1/\sigma$" is read for matrices.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3590–3593 (§1.2, §2, (2.1)–(2.5), Condition 2.3), pp. 3596–3598 ((4.1), Condition 4.1, (4.2), Condition 4.3), p. 3611 ((7.2))

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_GraphonMF_DenseRate_Setting
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- `I = [0,1]` (Mathlib's `unitInterval`, with Lebesgue measure as its `volume`). -/
scoped notation "I" => unitInterval

/-! ### Labels, graphons, the cut norm (Bayraktar–Chakraborty–Wu 2023, §2, p. 3590) -/

/-! ### Paths, the norms `‖·‖_{*,t}`, Wasserstein distances and the class `ℳ` (§1.2, §2) -/

instance (T : ℝ≥0) (d : ℕ) : BorelSpace (GraphonMF.Stability.Cd T d) := ⟨rfl⟩

open Classical in

/-! ### The continuum noise (p. 3591) -/

/-- The σ-algebra generated by all initial states `X_u(0)` and all Brownian paths `B_u`. -/
noncomputable abbrev noiseSigma {Ω : Type*} {d : ℕ} (X0 : I → Ω → Fin d → ℝ)
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) : MeasurableSpace Ω :=
  ⨆ u, (MeasurableSpace.comap (X0 u) inferInstance ⊔
    MeasurableSpace.comap (fun ω t => B u t ω) inferInstance)

/-- The standing noise of (2.1): a probability space carrying independent initial states
`X_u(0) ~ μ_u(0)` and i.i.d. standard `d`-dimensional Brownian motions `B_u`, `u ∈ I`, the whole
family `{X_u(0)} ∪ {B_u}` mutually independent. -/
structure NoiseSetting {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → Fin d → ℝ)
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  meas0 : ∀ u, Measurable (X0 u)
  law0 : ∀ u, P.map (X0 u) = μ0 u
  bm : ∀ u, Peng1990.SMP.IsStdBrownian P (B u)
  indep : iIndep (fun k : I ⊕ I => Sum.elim
      (fun u => MeasurableSpace.comap (X0 u) inferInstance)
      (fun u => MeasurableSpace.comap (fun ω t => B u t ω) inferInstance) k) P

/-- The filtration `𝓕ᵘ_t = σ(X_u(0), B_u(s) : s ≤ t)` of the graphon particle `X_u`. -/
noncomputable def filtU {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B) (u : I) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (fun t ω => (X0 u ω, B u t ω))
    (fun t => ((hN.meas0 u).prodMk ((hN.bm u).meas t)).stronglyMeasurable)

/-- The (natural, uncompleted) filtration of the `n`-particle system:
`𝓕ⁿ_t = σ(ξⁿ, X_{j/n}(0), B_{j/n}(s) : j ≤ n, s ≤ t)`. -/
noncomputable def filtN {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B) {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ}
    (hξ : ∀ n, Measurable (ξ n)) (n : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  { seq := fun t => ⨆ s ≤ t, MeasurableSpace.comap
      (fun ω => (ξ n ω, fun j : Fin n => X0 (GraphonMF.DenseRate.lab n j) ω, fun j : Fin n => B (GraphonMF.DenseRate.lab n j) s ω))
      inferInstance
    mono' := fun _ _ h => biSup_mono fun _ hs => le_trans hs h
    le' := fun _ => iSup₂_le fun s _ =>
      ((hξ n).prodMk ((measurable_pi_lambda _ fun j => hN.meas0 (GraphonMF.DenseRate.lab n j)).prodMk
        (measurable_pi_lambda _ fun j => (hN.bm (GraphonMF.DenseRate.lab n j)).meas s))).comap_le }

/-! ### Conditions 2.3, 4.1, 4.3 (pp. 3593, 3597, 3598) -/

/-- Condition 2.3 for a given finite cover `{J_i}` of `I` by intervals (order-connected sets):
some `κ > 0` makes `u ↦ μ_u(0)` `κ`-Lipschitz in `W₂` on each `J_i` and `G` `κ`-Lipschitz on each
block `J_i × J_j`. -/
def Cond23 {d : ℕ} (μ0 : I → Measure (Fin d → ℝ)) (G : I → I → ℝ) {N : ℕ}
    (J : Fin N → Set I) : Prop :=
  (∀ i, (J i).OrdConnected) ∧ (⋃ i, J i) = Set.univ ∧
    ∃ κ : ℝ, 0 < κ ∧
      (∀ i, ∀ u₁ ∈ J i, ∀ u₂ ∈ J i,
        GraphonMF.DenseRate.W2 (μ0 u₁) (μ0 u₂) ≤ ENNReal.ofReal (κ * |(u₁ : ℝ) - u₂|)) ∧
      (∀ i j, ∀ u₁ ∈ J i, ∀ u₂ ∈ J i, ∀ v₁ ∈ J j, ∀ v₂ ∈ J j,
        |G u₁ v₁ - G u₂ v₂| ≤ κ * (|(u₁ : ℝ) - u₂| + |(v₁ : ℝ) - v₂|))

/-- Condition 4.1(a): `u ↦ μ_u(0)` is measurable, each `μ_u(0)` is a probability measure, and
`sup_u 𝔼|X_u(0)|² < ∞`. -/
def Cond41a {d : ℕ} (μ0 : I → Measure (Fin d → ℝ)) : Prop :=
  Measurable μ0 ∧ (∀ u, IsProbabilityMeasure (μ0 u)) ∧ (⨆ u, ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ0 u)) < ⊤

/-- Condition 4.1(b): `b` is bounded and Lipschitz. -/
def Cond41b {d : ℕ} (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  (∃ C : ℝ, ∀ x y, ‖b x y‖ ≤ C) ∧
    ∃ K : ℝ, ∀ x x' y y', ‖b x y - b x' y'‖ ≤ K * (‖x - x'‖ + ‖y - y'‖)

/-- Condition 4.1(c): `σ` is bounded, Lipschitz, and invertible with bounded inverse (the
"`1/σ`" of the page read for `d × d` matrices; bounds entrywise). -/
def Cond41c {d : ℕ} (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∃ C : ℝ, ∀ x i j, |σ x i j| ≤ C) ∧
    (∃ K : ℝ, ∀ x x' i j, |σ x i j - σ x' i j| ≤ K * ‖x - x'‖) ∧
    (∀ x, IsUnit (σ x).det) ∧
    ∃ C : ℝ, ∀ x i j, |(σ x)⁻¹ i j| ≤ C

/-- Condition 4.1(d): `β_n ∈ (0,1]` for `n ≥ 1` and `nβ_n → ∞`. -/
def Cond41d (β : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → β n ∈ Set.Ioc (0 : ℝ) 1) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * β n) atTop atTop

/-- Condition 4.1 (p. 3597), parts (a)–(d). -/
def Cond41 {d : ℕ} (μ0 : I → Measure (Fin d → ℝ))
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (β : ℕ → ℝ) : Prop :=
  Cond41a μ0 ∧ Cond41b b ∧ Cond41c σ ∧ Cond41d β

/-- Condition 4.3: for every `n`, `ξⁿ_ij = ξⁿ_ji ~ Bernoulli(β_n G(i/n, j/n))`, independent over
`i ≤ j` (diagonal included), and independent of `{B_u, X_u(0) : u ∈ I}`. -/
structure Cond43 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (X0 : I → Ω → Fin d → ℝ) (B : I → ℝ≥0 → Ω → Fin d → ℝ)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (β : ℕ → ℝ) (G : I → I → ℝ) : Prop where
  meas : ∀ n, Measurable (ξ n)
  symm : ∀ n ω i j, ξ n ω i j = ξ n ω j i
  binary : ∀ n ω i j, ξ n ω i j = 0 ∨ ξ n ω i j = 1
  law : ∀ n i j, P {ω | ξ n ω i j = 1} = ENNReal.ofReal (β n * G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j))
  indep : ∀ n, iIndepFun (fun (p : {p : Fin n × Fin n // p.1 ≤ p.2}) ω => ξ n ω p.1.1 p.1.2) P
  indepNoise : ∀ n, Indep (MeasurableSpace.comap (ξ n) inferInstance) (noiseSigma X0 B) P

/-! ### The limit system (4.2) and the not-so-dense system (4.1) (pp. 3596–3597) -/

/-- The graphon-averaged drift `∫_I ∫_{ℝ^d} b(y, x) G(u, v) μ_{v,s}(dx) dv`, `μ_{v,s} = ℒ(X_v(s))`. -/
noncomputable def driftAvg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)) (G : I → I → ℝ)
    (X : I → ℝ≥0 → Ω → Fin d → ℝ) (u : I) (s : ℝ≥0) (y : Fin d → ℝ) : Fin d → ℝ :=
  ∫ v, G u v • ∫ x, b y x ∂(P.map (X v s))

/-- `X = (X_u)_{u ∈ I}` solves the graphon particle system (4.2) on `[0, T]`: continuous paths,
`X_u(0)` as given, path laws in `ℳ`, and each `X_u` a strong solution for its own filtration
`𝓕ᵘ` of `dX_u = ∫_I∫ b(X_u, x) G(u,v) μ_{v,s}(dx) dv ds + σ(X_u) dB_u`. -/
def IsGraphonSolution42 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B) (T : ℝ≥0)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (G : I → I → ℝ)
    (X : I → ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  (∀ u ω, ContinuousOn (fun s => X u s ω) (Set.Icc 0 T)) ∧
  (∀ u, X u 0 = X0 u) ∧
  (∀ u, AEMeasurable (GraphonMF.DenseRate.pathOf T (X u)) P) ∧
  GraphonMF.DenseRate.InM (fun u => P.map (GraphonMF.DenseRate.pathOf T (X u))) ∧
  ∀ u, Peng1990.SMP.IsItoProcess (filtU hN u) P T (B u) 0
    (fun s ω => driftAvg P b G X u s (X u s ω))
    (fun j s ω i => σ (X u s ω) i j)
    (fun t ω => X u t ω - X0 u ω)

/-- `Xⁿ = (Xⁿ_i)_{i ≤ n}` solves the not-so-dense system (4.1) on `[0, T]`: continuous paths,
`Xⁿ_i(0) = X_{i/n}(0)`, and each `Xⁿ_i` a strong solution for `𝓕ⁿ` of
`dXⁿ_i = (1/(nβ_n)) Σ_j ξⁿ_ij b(Xⁿ_i, Xⁿ_j) ds + σ(Xⁿ_i) dB_{i/n}`. -/
def IsParticleSolution41 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B) {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ}
    (hξ : ∀ n, Measurable (ξ n)) (T : ℝ≥0)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (β : ℕ → ℝ) (n : ℕ)
    (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ) : Prop :=
  (∀ i ω, ContinuousOn (fun s => Xn i s ω) (Set.Icc 0 T)) ∧
  (∀ i, Xn i 0 = X0 (GraphonMF.DenseRate.lab n i)) ∧
  (∀ i, AEMeasurable (GraphonMF.DenseRate.pathOf T (Xn i)) P) ∧
  ∀ i, Peng1990.SMP.IsItoProcess (filtN hN hξ n) P T (B (GraphonMF.DenseRate.lab n i)) 0
    (fun s ω => (1 / ((n : ℝ) * β n)) • ∑ j, ξ n ω i j • b (Xn i s ω) (Xn j s ω))
    (fun j s ω k => σ (Xn i s ω) k j)
    (fun t ω => Xn i t ω - X0 (GraphonMF.DenseRate.lab n i) ω)

/-! ### The terms `R^{n,2}_s`, `R^{n,4}_s` of (7.2) (p. 3611), with `G` in place of `G_n` -/

/-- `R^{n,2}_s = (1/n) Σ_i 𝔼 |(1/n) Σ_j (ξⁿ_ij/β_n)(b(X_{i/n}(s), Xⁿ_j(s)) − b(X_{i/n}(s), X_{j/n}(s)))|²`. -/
noncomputable def Rn2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)) (β : ℕ → ℝ)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (X : I → ℝ≥0 → Ω → Fin d → ℝ) (n : ℕ)
    (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
    ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
      (b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω))‖ₑ ^ 2 ∂P

/-- `R^{n,4}_s = (1/n) Σ_i 𝔼 |(1/n) Σ_j ∫ b(X_{i/n}(s), x) G(i/n, j/n) μ_{j/n,s}(dx)
− ∫_I ∫ b(X_{i/n}(s), x) G(i/n, v) μ_{v,s}(dx) dv|²`. -/
noncomputable def Rn4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)) (G : I → I → ℝ)
    (X : I → ℝ≥0 → Ω → Fin d → ℝ) (n : ℕ) (s : ℝ≥0) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
    ‖((1 / (n : ℝ)) • ∑ j : Fin n,
        G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))
      - driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P

end GraphonMF.SparseRate


