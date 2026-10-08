-- Prove2me | Definitions.Def_NonlinSSD_Optimality_Basic
-- name    : NonlinSSD_Optimality_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:43:22.043659+00:00
-- url     : https://prove2.me/theorems/0530be3e-fa6e-4be8-ad6b-35575bc79f55
-- title:
--   Problem (11)–(14), F₂ (4), the utility cone 𝒰₁([a,b]) (c ≥ 0), the Lagrangians L and Λ (22), the set C and uniform dominance (Definition 1)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and let $\mathcal Z$ be a separable locally convex Hausdorff real vector space. This file fixes the objects of §§2–3 of Dentcheva and Ruszczyński's paper on stochastic optimization with nonlinear dominance constraints.
--
--   1. **Second performance function** (4). For a random variable $X$ with $\mathbb E|X|<\infty$,
--   $$F_2(X;\eta)=\int_{-\infty}^{\eta}P[X\le\alpha]\,d\alpha,\qquad \eta\in\mathbb R.$$
--   2. **Utility cone** (p. 7). $\mathcal U_1([a,b])$ is the set of functions $u:\mathbb R\to\mathbb R$ that are concave and nondecreasing, satisfy $u(t)=0$ for all $t\ge b$, and satisfy $u(t)=u(a)+c\,(t-a)$ for all $t\le a$ with some constant $c\ge 0$.
--   3. **Superdifferential** (p. 3). For $f:\mathbb R^n\to\mathbb R$ and $y\in\mathbb R^n$, $\partial f(y)$ is the set of $\theta\in\mathbb R^n$ with $f(y')\le f(y)+\langle\theta,y'-y\rangle$ for all $y'$.
--   4. **Problem data** (p. 2). A convex set $Z\subseteq\mathcal Z$; operators $H,G_1,\dots,G_m$ from $\mathcal Z$ to $\mathcal L_1$, continuous in the $\mathcal L_1$ norm, such that for $P$-almost every $\omega$ the maps $z\mapsto[H(z)](\omega)$ and $z\mapsto[G_i(z)](\omega)$ are concave and continuous on $\mathcal Z$; reference outcomes $Y_i\in\mathcal L_1$; bounded intervals $[a_i,b_i]$.
--   5. **The split problem** (11)–(14):
--   $$\max\ \mathbb E[H(z)]\quad\text{s.t.}\quad F_2(X_i;\eta)\le F_2(Y_i;\eta)\ (\eta\in[a_i,b_i]),\quad G_i(z)\ge X_i\ \text{a.s.},\quad z\in Z,\ X_i\in\mathcal L_1 .$$
--   Feasibility and (attained) optimality are defined for it, together with the convex set $C=\{(z,X): z\in Z,\ X_i\in\mathcal L_1,\ X_i\le G_i(z)\text{ a.s.}\}$ of p. 8.
--   6. **Uniform dominance** (Definition 1): some $\tilde z\in Z$ has $\inf_{\eta\in[a_i,b_i]}\{F_2(Y_i;\eta)-F_2(G_i(\tilde z);\eta)\}>0$ for every $i$.
--   7. **Utility Lagrangian** (p. 7):
--   $$L(z,X,u,\theta)=\mathbb E\Big[H(z)+\sum_{i=1}^m\big(u_i(X_i)-u_i(Y_i)+\theta_i(G_i(z)-X_i)\big)\Big],$$
--   with $u\in\mathcal U_1^m=\prod_i\mathcal U_1([a_i,b_i])$ and $\theta\in\mathcal L_\infty^m$; the predicates "$(\hat z,\hat X)$ attains $\max_{(z,X)\in Z\times\mathcal L_1^m}L(z,X,u,\theta)$" (18) and the complementarity conditions (19)–(20).
--   8. **Measure Lagrangian** (22): $\Lambda(z,X,\mu)=\mathbb E[H(z)]+\sum_i\int_{[a_i,b_i]}\big(F_2(Y_i;\eta)-F_2(X_i;\eta)\big)\,d\mu_i(\eta)$ for nonnegative measures $\mu_i$.
--   9. **Utility of a measure** (p. 8): for a nonnegative measure $\mu$, $u(t)=-\int_t^b\mu([\tau,b])\,d\tau$ for $t<b$ and $u(t)=0$ for $t\ge b$.
--
--   These are the shared objects of the optimality conditions (Theorem 2 and its measure-multiplier steps) and of the dual-functional analysis of §4, which uses $\mathcal U_1([a,b])$.
--
--   **Formalization Note** The paper prints "with some $c>0$" in the definition of $\mathcal U_1([a,b])$; this is corrected to $c\ge 0$, because the page calls $\mathcal U_1$ a convex cone (it must contain $0$) and with $c>0$ Theorem 2 fails whenever a dominance constraint is slack at the optimum. Random variables are functions $\Omega\to\mathbb R$ carrying `Integrable` ($\mathcal L_1$) or `MemLp · ⊤` ($\mathcal L_\infty$); $F_2$ is a Bochner integral, finite for integrable $X$. The operators are given by their realizations $z\mapsto(\omega\mapsto[H(z)](\omega))$, integrable for each $z$; $\mathcal L_1$ continuity is $\int|H(z)-H(z_0)|\,dP\to 0$ as $z\to z_0$; the almost-sure concavity and continuity are stated with one null set for all $z$, as the paper's "for $P$-almost all $\omega$". The intervals satisfy $a_i\le b_i$. Definition 1's infimum is encoded as a uniform positive lower bound $\varepsilon_i$ on $[a_i,b_i]$, which is equivalent. "$\theta\in\mathcal L_\infty^m$, $\theta\ge 0$ a.s." is one predicate. The Lagrangian $L$ is a Bochner integral, meaningful when $X\in\mathcal L_1^m$, $u\in\mathcal U_1^m$ and $\theta\in\mathcal L_\infty^m$; the maximum (18) ranges over integrable $X$ only. $\Lambda$ is defined for nonnegative measures on $\mathbb R$ integrated over the closed interval (endpoint atoms included); finiteness and support in $[a_i,b_i]$ are hypotheses of the theorems that use it. $F_2$ here has the same body as the published `DualSSD.Shared.secondPerformance`.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), pp. 2–4, 7–8, Eqs. (1)–(4), (11)–(14), (22), Definition 1

import Mathlib

namespace NonlinSSD.Optimality

open MeasureTheory Filter

/-- The second performance function (4), p. 2: `F₂(X; η) = ∫_{−∞}^η P[X ≤ α] dα`, a Bochner
integral over `(−∞, η]`. It is finite for integrable `X`; every use takes `X ∈ 𝓛₁`. The body is
the same integral as the published `DualSSD.Shared.secondPerformance`. -/
noncomputable def F2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (η : ℝ) : ℝ :=
  ∫ ξ in Set.Iic η, P.real {ω | X ω ≤ ξ}

/-- The corrected utility cone on `[a,b]`, p. 7. The printed `c > 0` is a typo: the
zero utility must belong to the cone, and the theorem fails with strict positivity. -/
def U1 (a b : ℝ) : Set (ℝ → ℝ) :=
  {u | ConcaveOn ℝ Set.univ u ∧ Monotone u ∧
    (∀ t, b ≤ t → u t = 0) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ≤ a, u t = u a + c * (t - a)}

/-- A finite-dimensional concave superdifferential, using the sign convention on p. 3. -/
def superdiff {n : ℕ} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {θ | ∀ y' : Fin n → ℝ,
    f y' ≤ f y + ∑ i, θ i * (y' i - y i)}

/-- The data of the split stochastic optimization problem (11)–(14). The operators are
represented by integrable realizations; `H_L1_cont` and `G_L1_cont` express continuity
in the L¹ norm, and the realization conditions use one null set for all decisions. -/
structure Problem (Ω 𝒵 : Type*) [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : ℕ) where
  Z : Set 𝒵
  Z_convex : Convex ℝ Z
  H : 𝒵 → Ω → ℝ
  G : Fin m → 𝒵 → Ω → ℝ
  Y : Fin m → Ω → ℝ
  a : Fin m → ℝ
  b : Fin m → ℝ
  interval_nonempty : ∀ i, a i ≤ b i
  H_integrable : ∀ z, Integrable (H z) P
  G_integrable : ∀ i z, Integrable (G i z) P
  Y_integrable : ∀ i, Integrable (Y i) P
  H_L1_cont : ∀ z₀, Tendsto
    (fun z => ∫ ω, |H z ω - H z₀ ω| ∂P) (nhds z₀) (nhds 0)
  G_L1_cont : ∀ i z₀, Tendsto
    (fun z => ∫ ω, |G i z ω - G i z₀ ω| ∂P) (nhds z₀) (nhds 0)
  H_sample : ∀ᵐ ω ∂P, ConcaveOn ℝ Set.univ (fun z => H z ω) ∧
    Continuous (fun z => H z ω)
  G_sample : ∀ i, ∀ᵐ ω ∂P, ConcaveOn ℝ Set.univ (fun z => G i z ω) ∧
    Continuous (fun z => G i z ω)

namespace Problem

variable {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

/-- (12): dominance on the specified bounded interval. -/
def Dominates (pr : Problem Ω 𝒵 P m) (X : Fin m → Ω → ℝ) : Prop :=
  ∀ i η, η ∈ Set.Icc (pr.a i) (pr.b i) →
    F2 P (X i) η ≤ F2 P (pr.Y i) η

/-- (11)–(14): the split problem's feasible points. -/
def Feasible (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) : Prop :=
  z ∈ pr.Z ∧ (∀ i, Integrable (X i) P) ∧
  pr.Dominates X ∧ ∀ i, X i ≤ᵐ[P] pr.G i z

/-- An attained optimum of (11)–(14). -/
def IsOptimal (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) : Prop :=
  pr.Feasible z X ∧
  ∀ z' X', pr.Feasible z' X' →
    (∫ ω, pr.H z' ω ∂P) ≤ ∫ ω, pr.H z ω ∂P

/-- Definition 1, p. 7. A positive uniform lower bound replaces the real infimum. -/
def UniformDominance (pr : Problem Ω 𝒵 P m) : Prop :=
  ∃ zt, zt ∈ pr.Z ∧ ∀ i, ∃ ε : ℝ, 0 < ε ∧
    ∀ η ∈ Set.Icc (pr.a i) (pr.b i),
      ε ≤ F2 P (pr.Y i) η - F2 P (pr.G i zt) η

/-- `𝒰₁ᵐ`, the product of the utility cones. -/
def UtilityAdmissible (pr : Problem Ω 𝒵 P m)
    (u : Fin m → ℝ → ℝ) : Prop :=
  ∀ i, u i ∈ U1 (pr.a i) (pr.b i)

/-- `𝓛∞ᵐ` with nonnegative coordinates, as in (20). -/
def MultiplierAdmissible (pr : Problem Ω 𝒵 P m)
    (θ : Fin m → Ω → ℝ) : Prop :=
  (∀ i, MemLp (θ i) ⊤ P) ∧ ∀ i, 0 ≤ᵐ[P] θ i

/-- The utility Lagrangian `L` of p. 7. Its theorem-level domain is `X ∈ 𝓛¹ᵐ`,
`u ∈ 𝒰₁ᵐ` and `θ ∈ 𝓛∞ᵐ`, where the integrand is integrable. -/
noncomputable def L (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) (u : Fin m → ℝ → ℝ)
    (θ : Fin m → Ω → ℝ) : ℝ :=
  ∫ ω, pr.H z ω + ∑ i : Fin m,
    (u i (X i ω) - u i (pr.Y i ω) + θ i ω * (pr.G i z ω - X i ω)) ∂P

/-- Attained maximum of the utility Lagrangian over `Z × 𝓛¹ᵐ`, equation (18). -/
def MaximizesL (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) (u : Fin m → ℝ → ℝ)
    (θ : Fin m → Ω → ℝ) : Prop :=
  z ∈ pr.Z ∧ (∀ i, Integrable (X i) P) ∧
  ∀ z' ∈ pr.Z, ∀ X' : Fin m → Ω → ℝ,
    (∀ i, Integrable (X' i) P) →
      pr.L z' X' u θ ≤ pr.L z X u θ

/-- Equations (19)–(20) at a candidate solution. -/
def Complementary (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) (u : Fin m → ℝ → ℝ)
    (θ : Fin m → Ω → ℝ) : Prop :=
  (∀ i, (∫ ω, u i (X i ω) ∂P) = ∫ ω, u i (pr.Y i ω) ∂P) ∧
  ∀ i, (fun ω => θ i ω * (X i ω - pr.G i z ω)) =ᵐ[P] (fun _ => 0)

/-- The convex set `C` of p. 8, before imposing the dominance constraint. -/
def InC (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) : Prop :=
  z ∈ pr.Z ∧ (∀ i, Integrable (X i) P) ∧
  ∀ i, X i ≤ᵐ[P] pr.G i z

/-- Equation (22): the measure Lagrangian over closed intervals, including endpoint atoms. -/
noncomputable def Lambda (pr : Problem Ω 𝒵 P m) (z : 𝒵)
    (X : Fin m → Ω → ℝ) (μ : Fin m → Measure ℝ) : ℝ :=
  (∫ ω, pr.H z ω ∂P) +
    ∑ i : Fin m, ∫ η in Set.Icc (pr.a i) (pr.b i),
      (F2 P (pr.Y i) η - F2 P (X i) η) ∂μ i

end Problem

/-- The p. 8 utility associated with a finite nonnegative measure. -/
noncomputable def uOfMeasure (μ : Measure ℝ) (b t : ℝ) : ℝ :=
  if t < b then -∫ τ in t..b, μ.real (Set.Icc τ b) else 0

end NonlinSSD.Optimality


