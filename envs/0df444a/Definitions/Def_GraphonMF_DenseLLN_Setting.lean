-- Prove2me | Definitions.Def_GraphonMF_DenseLLN_Setting
-- name    : GraphonMF_DenseLLN_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:48.46698+00:00
-- url     : https://prove2.me/theorems/d88f7ae3-4add-4805-b856-b9c719707de5
-- title:
--   §1.2–§3, §6.1, pp. 3590–3605 — graphons, cut and operator norms, 𝒞_d, W₂, ℳ, the continuum noise, solutions of (2.1) and (3.1), Conditions 2.1, 2.2, 3.1(b), μⁿ, μ̄, T^{n,2}, T^{n,3}
-- statement:
--   This file fixes the objects of the law of large numbers for dense graphon-weighted particle systems (Bayraktar, Chakraborty and Wu, *Graphon mean field systems*, §2–§3).
--
--   **Labels and graphons.** Write $I=[0,1]$ with Lebesgue measure. Particle $i\in\{1,\dots,n\}$ carries the label $i/n\in I$. A **graphon** is a measurable symmetric function $G:I\times I\to[0,1]$. The **cut norm** and the **operator norm** of a bounded measurable kernel $W$ are
--   $$\|W\|_\square=\sup_{S,T\in\mathcal B(I)}\Big|\int_{S\times T}W(u,v)\,du\,dv\Big|,\qquad \|W\|=\|W\|_{\infty\to1}=\sup_{\|g\|_\infty\le1}\int_I\Big|\int_I W(u,v)g(v)\,dv\Big|\,du .$$
--   A **step graphon** on the $n$-grid is a graphon with $G_n(u,v)=G_n(\lceil nu\rceil/n,\lceil nv\rceil/n)$ (display (3.2)).
--
--   **Paths and distances.** Fix $T>0$. The path space is $\mathcal C_d=C([0,T]:\mathbb R^d)$ with the uniform norm $\|x\|_{*,T}=\sup_{0\le s\le T}|x_s|$ and its Borel σ-algebra. $W_2$ on $\mathcal P(\mathbb R^d)$ and $W_{2,T}$ on $\mathcal P(\mathcal C_d)$ are the Wasserstein-2 distances (2.3)–(2.4). The class $\mathcal M$ consists of measurable families $u\mapsto\nu_u\in\mathcal P(\mathcal C_d)$ with $\sup_u\int\|x\|_{*,T}^2\,\nu_u(dx)<\infty$.
--
--   **Conditions.** Condition 2.1: $u\mapsto\mu_u(0)$ is measurable, $\sup_u\mathbb E|X_u(0)|^{2+\varepsilon}<\infty$ for some $\varepsilon>0$, and $b,\sigma$ are Lipschitz. Condition 2.2, for a finite cover of $I$ by intervals $I_1,\dots,I_N$: (a) $u\mapsto\mu_u(0)$ is $W_2$-continuous on each $I_i$; (b) for each interior point $u$ of $I_i$, $G$ is continuous at $(u,v)$ for Lebesgue-a.e. $v$.
--
--   **Noise and the graphon particle system (2.1).** One probability space carries independent initial states $X_u(0)\sim\mu_u(0)$ and $d$-dimensional Brownian motions $B_u$, $u\in I$, the whole family mutually independent. A solution of (2.1) is a family of continuous processes $X_u$ with laws $\mu_u$ in $\mathcal M$ such that
--   $$X_u(t)=X_u(0)+\int_0^t\!\!\int_I\!\int_{\mathbb R^d} b(X_u(s),x)G(u,v)\mu_{v,s}(dx)\,dv\,ds+\int_0^t\!\!\int_I\!\int_{\mathbb R^d}\sigma(X_u(s),x)G(u,v)\mu_{v,s}(dx)\,dv\,dB_u(s),$$
--   with $\mu_{v,s}$ the law of $X_v(s)$.
--
--   **The $n$-particle system (3.1).** With weights $\xi^n_{ij}$,
--   $$X^n_i(t)=X_{i/n}(0)+\int_0^t\frac1n\sum_{j=1}^n\xi^n_{ij}b(X^n_i(s),X^n_j(s))\,ds+\int_0^t\frac1n\sum_{j=1}^n\xi^n_{ij}\sigma(X^n_i(s),X^n_j(s))\,dB_{i/n}(s).$$
--   The $n$-particle system uses the same initial states and Brownian motions as the graphon system at the labels $i/n$. Condition 3.1(b): either $\xi^n_{ij}=G_n(i/n,j/n)$ for all $n,i,j$, or for all $n$ the $\xi^n_{ij}=\xi^n_{ji}$ are Bernoulli$(G_n(i/n,j/n))$, independent for $i\le j$ and independent of the noise.
--
--   **Empirical measures and the terms of (6.2).** $\mu^n=\frac1n\sum_i\delta_{X^n_i}$, $\bar\mu=\int_I\mu_u\,du$, and convergence in probability in $\mathcal P(\mathcal C_d)$ (weak topology) means $\mathbb P(\mu^n\notin U)\to0$ for every neighbourhood $U$ of the limit. The terms $\mathcal T^{n,2}_s$, $\mathcal T^{n,3}_s$ are the second and third averages of the decomposition (6.2):
--   $$\mathcal T^{n,2}_s=\frac1n\sum_{i}\mathbb E\Big|\frac1n\sum_{j}\Big(\xi^n_{ij}b(X_{i/n}(s),X_{j/n}(s))-\int b(X_{i/n}(s),x)G_n(\tfrac in,\tfrac jn)\mu_{j/n,s}(dx)\Big)\Big|^2,$$
--   $$\mathcal T^{n,3}_s=\frac1n\sum_{i}\mathbb E\Big|\frac1n\sum_{j}\int b(X_{i/n}(s),x)G_n(\tfrac in,\tfrac jn)\mu_{j/n,s}(dx)-\int_I\!\int b(X_{i/n}(s),x)G(\tfrac in,v)\mu_{v,s}(dx)\,dv\Big|^2.$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with the sup norm, and matrices are measured by their largest entry. Every statement of the paper is invariant under this choice: all constants are existential and the other conclusions are limits. Processes are path-valued, $X_u:\Omega\to\mathcal C_d$, and $x(s)$ for $s>T$ is read as $x(T)$; only $s\le T$ is used. Particle $i\in\{1,\dots,n\}$ is Lean's `i : Fin n` with label $(i+1)/n$. Each SDE is encoded as in Peng's published `IsItoProcess`: $X-X(0)$ is an Itô process for the uncompleted natural filtration $\sigma(X_u(0),B_u(r):r\le t)$ (graphon system) or $\sigma(\xi^n,X_{j/n}(0),B_{j/n}(r):j\le n,r\le t)$ ($n$-particle system). The independence assumptions make each driving $B$ a Brownian motion for that filtration. A solution of (2.1) carries membership of its law family in $\mathcal M$ (measurability of $u\mapsto\mu_u$ for the Giry σ-algebra, which on the Polish space $\mathcal C_d$ is the Borel σ-algebra of the weak topology, and bounded second moments). This is the solution class of Proposition 2.1, and it makes every Bochner integral in the drift and diffusion meaningful. Path maps are required to be a.e. measurable. The definition of the $n$-particle filtration needs each $\xi^n$ to be measurable. Expectations of nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$, and Wasserstein distances take values in $[0,\infty]$. An "interval" of Condition 2.2 is an order-connected subset of $I$, and "interior point" means interior in $\mathbb R$. In case (b.2) the Bernoulli variables take values in $\{0,1\}$ at every $\omega$. $\mu^n$ for $n=0$ and $\bar\mu$ outside $\mathcal M$ are placeholders $\delta_0$, irrelevant for limits $n\to\infty$ and for solutions of (2.1).
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3590–3595, §1.2, §2, (2.1)–(2.4), Conditions 2.1, 2.2, (3.1), (3.2), Condition 3.1, Theorem 3.1; pp. 3604–3605, (6.2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_GraphonMF_Stability_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN

/-! ### Labels, graphons, cut norm, operator norm (§2, p. 3590; (3.2), p. 3594) -/

/-! ### Paths, Wasserstein distances, the class ℳ (§1.2, p. 3590; (2.3)–(2.4), p. 3592) -/

instance pathBorel (T : ℝ≥0) (d : ℕ) : BorelSpace (GraphonMF.Stability.Cd T d) := ⟨rfl⟩

/-! ### Conditions 2.1 and 2.2 (pp. 3591–3593) -/

/-- A finite cover of `I` by intervals `I_1, …, I_N` (order-connected subsets of `I`). -/
def IsIntervalCover {N : ℕ} (J : Fin N → Set GraphonMF.Stability.I) : Prop :=
  (∀ i, (J i).OrdConnected) ∧ (⋃ i, J i) = Set.univ

/-- Condition 2.2(a) for the cover `J`: on each `I_i`, `u ↦ μ_u(0)` is `W₂`-continuous. -/
def Cond22a {d N : ℕ} (μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)) (J : Fin N → Set GraphonMF.Stability.I) : Prop :=
  IsIntervalCover J ∧
    ∀ i, ∀ u ∈ J i, Tendsto (fun v => GraphonMF.Stability.W2 (μ0 v) (μ0 u)) (𝓝[J i] u) (𝓝 0)

/-- Condition 2.2(b) for the cover `J`: for each interior point `u` of `I_i` (interior in `ℝ`)
there is a Lebesgue-null `A_u ⊂ GraphonMF.Stability.I` such that `G` is continuous at `(u, v)` for all `v ∉ A_u`. -/
def Cond22b {N : ℕ} (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (J : Fin N → Set GraphonMF.Stability.I) : Prop :=
  IsIntervalCover J ∧
    ∀ i, ∀ u : GraphonMF.Stability.I, (u : ℝ) ∈ interior (Subtype.val '' J i) →
      ∃ A : Set GraphonMF.Stability.I, volume A = 0 ∧ ∀ v, v ∉ A → ContinuousAt (Function.uncurry G) (u, v)

/-! ### The continuum noise and the graphon particle system (2.1), p. 3591 -/

/-- The noise of §1/§2: a probability space carrying the initial states `X_u(0) ~ μ_u(0)` and
standard `d`-dimensional Brownian motions `B_u`, the whole family
`{X_u(0) : u ∈ GraphonMF.Stability.I} ∪ {B_u : u ∈ GraphonMF.Stability.I}` mutually independent. -/
structure NoiseSetting {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)) (X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d) :
    Prop where
  prob : IsProbabilityMeasure P
  initial_meas : ∀ u, Measurable (X0 u)
  initial_law : ∀ u, P.map (X0 u) = μ0 u
  brownian : ∀ u, Peng1990.SMP.IsStdBrownian P (B u)
  indep : iIndep (fun z : GraphonMF.Stability.I ⊕ GraphonMF.Stability.I => match z with
      | Sum.inl u => MeasurableSpace.comap (X0 u) inferInstance
      | Sum.inr u => MeasurableSpace.comap (fun ω t => B u t ω) inferInstance) P

/-- The noise σ-algebra `σ(X_u(0), B_u : u ∈ GraphonMF.Stability.I)`. -/
abbrev noiseSigma {Ω : Type*} {d : ℕ} (X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d) :
    MeasurableSpace Ω :=
  ⨆ u, (MeasurableSpace.comap (X0 u) inferInstance ⊔
    MeasurableSpace.comap (fun ω t => B u t ω) inferInstance)

/-- The natural filtration `𝓕ᵘ_t = σ(X_u(0), B_u(s) : s ≤ t)` of particle `u`. -/
noncomputable def filtU {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (h : NoiseSetting P μ0 X0 B) (u : GraphonMF.Stability.I) : Filtration ℝ≥0 mΩ :=
  Filtration.natural (fun t ω => (X0 u ω, B u t ω))
    (fun t => ((h.initial_meas u).prodMk ((h.brownian u).meas t)).stronglyMeasurable)

/-- The drift of (2.1) at label `u`, time `s`, state `z`:
`∫_I ∫_{ℝᵈ} b(z, x) G(u,v) μ_{v,s}(dx) dv`. -/
noncomputable def graphonDrift {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ}
    (P : Measure Ω) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (u : GraphonMF.Stability.I) (s : ℝ≥0) (z : GraphonMF.Stability.State d) : GraphonMF.Stability.State d :=
  ∫ v, ∫ x, G u v • b z x ∂(GraphonMF.Stability.marginal (GraphonMF.Stability.law P X v) s)

/-- Column `j` of the diffusion of (2.1): `i ↦ ∫_I ∫_{ℝᵈ} σ_{ij}(z, x) G(u,v) μ_{v,s}(dx) dv`. -/
noncomputable def graphonDiff {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ}
    (P : Measure Ω) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (u : GraphonMF.Stability.I) (j : Fin d) (s : ℝ≥0) (z : GraphonMF.Stability.State d) : GraphonMF.Stability.State d :=
  fun i => ∫ v, ∫ x, G u v * σ z x i j ∂(GraphonMF.Stability.marginal (GraphonMF.Stability.law P X v) s)

/-- `X = (X_u)_{u ∈ GraphonMF.Stability.I}` (path-valued) solves the graphon particle system (2.1) for `G` on `[0,T]`:
the GraphonMF.Stability.law family is in `ℳ`; each path map is a.e. measurable; `X_u(0)` is the given initial state;
and `X_u − X_u(0)` is an Itô process for `𝓕ᵘ`, driven by `B_u`, with the drift and diffusion
of (2.1) evaluated at `X_u(s)` and the marginals `μ_{v,s}` of the solution's own laws. -/
def IsGraphonSolution {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d)
    (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) : Prop :=
  GraphonMF.Stability.InM (GraphonMF.Stability.law P X) ∧
    ∀ u, AEMeasurable (X u) P ∧ (∀ ω, GraphonMF.Stability.evalAt 0 (X u ω) = X0 u ω) ∧
      Peng1990.SMP.IsItoProcess (filtU noise u) P T (B u) 0
        (fun s ω => graphonDrift P G b X u s (GraphonMF.Stability.evalAt s (X u ω)))
        (fun j s ω => graphonDiff P G σ X u j s (GraphonMF.Stability.evalAt s (X u ω)))
        (fun s ω => GraphonMF.Stability.evalAt s (X u ω) - X0 u ω)

/-! ### The n-particle system (3.1) and Condition 3.1(b), pp. 3594–3595 -/

/-- Condition 3.1(b): either (b.1) `ξⁿ_ij = Gₙ(i/n, j/n)` for all `n, i, j`, or (b.2) for every
`n`, `ξⁿ_ij = ξⁿ_ji ∈ {0,1}` with `P(ξⁿ_ij = 1) = Gₙ(i/n, j/n)`, the family `{ξⁿ_ij : i ≤ j}`
mutually independent, and `ξⁿ` independent of `σ(X_u(0), B_u : u ∈ GraphonMF.Stability.I)`. -/
def Cond31b {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d)
    (B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d) (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) : Prop :=
  (∀ n ω i j, ξ n ω i j = Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j)) ∨
    ∀ n, (∀ ω i j, ξ n ω i j = ξ n ω j i) ∧ (∀ ω i j, ξ n ω i j = 0 ∨ ξ n ω i j = 1) ∧
      (∀ i j, P {ω | ξ n ω i j = 1} = ENNReal.ofReal (Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j))) ∧
      iIndepFun (fun (p : {p : Fin n × Fin n // p.1 ≤ p.2}) ω => ξ n ω p.1.1 p.1.2) P ∧
      Indep (MeasurableSpace.comap (ξ n) inferInstance) (noiseSigma X0 B) P

set_option synthInstance.maxSize 512 in
/-- The filtration of the `n`-particle system:
`𝓕ⁿ_t = σ(ξⁿ, X_{j/n}(0), B_{j/n}(s) : j ≤ n, s ≤ t)`. -/
noncomputable def filtN {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (h : NoiseSetting P μ0 X0 B) (n : ℕ) (ξn : Ω → Fin n → Fin n → ℝ) (hξ : Measurable ξn) :
    Filtration ℝ≥0 mΩ :=
  Filtration.natural (β := fun _ => (Fin n → Fin n → ℝ) × (Fin n → GraphonMF.Stability.State d) × (Fin n → GraphonMF.Stability.State d))
    (fun t ω => (ξn ω, fun j => X0 (GraphonMF.Stability.lab n j) ω, fun j => B (GraphonMF.Stability.lab n j) t ω))
    (fun t => (hξ.prodMk ((measurable_pi_lambda _ fun j => h.initial_meas (GraphonMF.Stability.lab n j)).prodMk
      (measurable_pi_lambda _ fun j => (h.brownian (GraphonMF.Stability.lab n j)).meas t))).stronglyMeasurable)

/-- `Xn = (Xⁿ_1, …, Xⁿ_n)` (path-valued) solves (3.1) on `[0,T]`: each path map is a.e.
measurable; `Xⁿ_i(0) = X_{i/n}(0)`; and `Xⁿ_i − X_{i/n}(0)` is an Itô process for `𝓕ⁿ`, driven by
`B_{i/n}`, with drift `(1/n) Σⱼ ξⁿ_ij b(Xⁿ_i(s), Xⁿ_j(s))` and diffusion
`(1/n) Σⱼ ξⁿ_ij σ(Xⁿ_i(s), Xⁿ_j(s))`. -/
def IsParticleSolution {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d)
    (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (ξn : Ω → Fin n → Fin n → ℝ)
    (hξ : Measurable ξn) (Xn : Fin n → Ω → GraphonMF.Stability.Cd T d) : Prop :=
  ∀ i, AEMeasurable (Xn i) P ∧ (∀ ω, GraphonMF.Stability.evalAt 0 (Xn i ω) = X0 (GraphonMF.Stability.lab n i) ω) ∧
    Peng1990.SMP.IsItoProcess (filtN noise n ξn hξ) P T (B (GraphonMF.Stability.lab n i)) 0
      (fun s ω => (1 / (n : ℝ)) • ∑ j, ξn ω i j • b (GraphonMF.Stability.evalAt s (Xn i ω)) (GraphonMF.Stability.evalAt s (Xn j ω)))
      (fun k s ω i' => (1 / (n : ℝ)) *
        ∑ j, ξn ω i j * σ (GraphonMF.Stability.evalAt s (Xn i ω)) (GraphonMF.Stability.evalAt s (Xn j ω)) i' k)
      (fun s ω => GraphonMF.Stability.evalAt s (Xn i ω) - X0 (GraphonMF.Stability.lab n i) ω)

/-! ### Empirical measures, the averaged GraphonMF.Stability.law, convergence in probability -/

/-- The empirical measure `(1/n) Σᵢ δ_{xᵢ}` of `n` paths. -/
noncomputable def empiricalMeasure {T : ℝ≥0} {d n : ℕ} (x : Fin n → GraphonMF.Stability.Cd T d) : Measure (GraphonMF.Stability.Cd T d) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

lemma isProbabilityMeasure_empiricalMeasure {T : ℝ≥0} {d n : ℕ} (hn : 0 < n)
    (x : Fin n → GraphonMF.Stability.Cd T d) : IsProbabilityMeasure (empiricalMeasure x) := by
  constructor
  have h0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  simp [empiricalMeasure, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top n)]

/-- The empirical measure as an element of `𝒫(𝒞_d)` (weak topology); for `n = 0`, where it is
undefined, a fixed placeholder `δ_0` (irrelevant for limits `n → ∞`). -/
noncomputable def empiricalPM {T : ℝ≥0} {d n : ℕ} (x : Fin n → GraphonMF.Stability.Cd T d) : ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  if hn : 0 < n then ⟨empiricalMeasure x, isProbabilityMeasure_empiricalMeasure hn x⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- The averaged GraphonMF.Stability.law `μ̄ = ∫_I μ_u du` of a labelled process, `(volume on GraphonMF.Stability.I).bind ℒ(X_·)`. -/
noncomputable def mixture {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} (P : Measure Ω)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) : Measure (GraphonMF.Stability.Cd T d) :=
  (volume : Measure GraphonMF.Stability.I).bind (GraphonMF.Stability.law P X)

open Classical in
/-- `μ̄` as an element of `𝒫(𝒞_d)`. It is a probability measure whenever the GraphonMF.Stability.law family is in
`ℳ` (as for every solution of (2.1)); otherwise a placeholder `δ_0`. -/
noncomputable def mixturePM {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} (P : Measure Ω)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) : ProbabilityMeasure (GraphonMF.Stability.Cd T d) :=
  if h : IsProbabilityMeasure (mixture P X) then ⟨mixture P X, h⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- Convergence in probability in `𝒫(𝒞_d)` (weak topology) of random probability measures:
for every neighbourhood `U` of `μ`, `P(Yₙ ∉ U) → 0` (outer measure). -/
def TendstoInProb {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} (P : Measure Ω)
    (Y : ℕ → Ω → ProbabilityMeasure (GraphonMF.Stability.Cd T d)) (μ : ProbabilityMeasure (GraphonMF.Stability.Cd T d)) : Prop :=
  ∀ U ∈ 𝓝 μ, Tendsto (fun n => P {ω | Y n ω ∉ U}) atTop (𝓝 0)

/-! ### The terms `T^{n,2}_s` and `T^{n,3}_s` of (6.2), pp. 3604–3605 -/

/-- `T^{n,2}_s = (1/n) Σᵢ E|(1/n) Σⱼ (ξⁿ_ij b(X_{i/n}(s), X_{j/n}(s))
 − ∫ b(X_{i/n}(s), x) Gₙ(i/n, j/n) μ_{j/n,s}(dx))|²`. -/
noncomputable def Tn2 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} (P : Measure Ω)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (n : ℕ) (s : ℝ≥0) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
    ‖(1 / (n : ℝ)) • ∑ j : Fin n,
      (ξ n ω i j • b (GraphonMF.Stability.evalAt s (X (GraphonMF.Stability.lab n i) ω)) (GraphonMF.Stability.evalAt s (X (GraphonMF.Stability.lab n j) ω)) -
        ∫ x, Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j) • b (GraphonMF.Stability.evalAt s (X (GraphonMF.Stability.lab n i) ω)) x
          ∂(GraphonMF.Stability.marginal (GraphonMF.Stability.law P X (GraphonMF.Stability.lab n j)) s))‖ₑ ^ 2 ∂P

/-- `T^{n,3}_s = (1/n) Σᵢ E|(1/n) Σⱼ ∫ b(X_{i/n}(s), x) Gₙ(i/n, j/n) μ_{j/n,s}(dx)
 − ∫_I ∫ b(X_{i/n}(s), x) G(i/n, v) μ_{v,s}(dx) dv|²`. -/
noncomputable def Tn3 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d : ℕ} (P : Measure Ω)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (n : ℕ) (s : ℝ≥0) : ℝ≥0∞ :=
  (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
    ‖(1 / (n : ℝ)) • ∑ j : Fin n,
        ∫ x, Gs n (GraphonMF.Stability.lab n i) (GraphonMF.Stability.lab n j) • b (GraphonMF.Stability.evalAt s (X (GraphonMF.Stability.lab n i) ω)) x
          ∂(GraphonMF.Stability.marginal (GraphonMF.Stability.law P X (GraphonMF.Stability.lab n j)) s) -
      graphonDrift P G b X (GraphonMF.Stability.lab n i) s (GraphonMF.Stability.evalAt s (X (GraphonMF.Stability.lab n i) ω))‖ₑ ^ 2 ∂P

end GraphonMF.DenseLLN


