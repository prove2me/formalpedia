-- Prove2me | Definitions.Def_ManyServerQED_Scheduling_Diffusion
-- name    : ManyServerQED_Scheduling_Diffusion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:39:37.217584+00:00
-- url     : https://prove2.me/theorems/061d49c7-9131-48e8-a186-5d5b5559671f
-- title:
--   The diffusion control problem: drift $b$, cost assumptions, admissible systems, value $V$, Hamiltonian $H$ and the HJB equation (41)
-- statement:
--   This file sets up the **diffusion control problem** of Section 2.5 and the HJB equation of Section 3.3. Throughout, $k\ge1$ is the number of customer classes, vectors of $\mathbb R^k$ are column vectors, $\|x\|=\sum_i|x_i|$ is the $\ell^1$ norm, $\mathbb 1=(1,\dots,1)'$, and $\mathbb S^k=\{u\in\mathbb R^k_+:\sum_iu_i=1\}$ is the simplex.
--
--   **Diffusion data.** The data are vectors $\ell\in\mathbb R^k$, $\mu\in(0,\infty)^k$, $\theta\in[0,\infty)^k$ and $r\in(0,\infty)^k$, and the drift (26) is
--   $$
--   b(x,u)=\ell+(\mu-\theta)(\mathbb 1\cdot x)^+u-\mu x,\qquad x\in\mathbb R^k,\ u\in\mathbb S^k,
--   $$
--   with $\mu=\operatorname{diag}(\mu_i)$, $\theta=\operatorname{diag}(\theta_i)$.
--
--   **Costs.** Given a queueing cost $\tilde L:\mathbb R^k\times\mathbb R^k\to\mathbb R$, the running cost (21) is $L(x,u)=\tilde L((\mathbb 1\cdot x)^+u,\;x-(\mathbb 1\cdot x)^+u)$. The hypotheses "$L$ is continuous and satisfies Assumption 2(i), (iii), (iv)" are: $L$ is continuous on $\mathbb R^k\times\mathbb S^k$; $L\ge0$ there; for some $\varrho\in(0,1)$ and every compact $A$ there is $c_A$ with $|L(x,u)-L(y,u)|\le c_A\|x-y\|^\varrho$ for $x,y\in A$, $u\in\mathbb S^k$; and for some $m_L\ge0$, $c>0$, $L(x,u)\le c(1+\|x\|^{m_L})$. Assumption 2 adds continuity of $\tilde L$.
--
--   **Admissible systems** (Definition 4). An admissible system $\pi=(\Omega,\mathcal F,(\mathcal F_t),P,u,W)$ consists of a complete filtered probability space, an $\mathbb S^k$-valued progressively measurable control $u$, and a standard $k$-dimensional $(\mathcal F_t)$-Brownian motion $W$. A **controlled process** for $x\in\mathbb R^k$ and $\pi$ is a continuous adapted process with $\int_0^t|b(X_s,u_s)|\,ds<\infty$ and
--   $$
--   X(t)=x+rW(t)+\int_0^tb(X(s),u(s))\,ds,\qquad t\ge0,\quad P\text{-a.s.}\qquad(27)
--   $$
--   The cost and the value are
--   $$
--   C(x,\pi)=E^\pi_x\int_0^\infty e^{-\gamma t}L(X(t),u(t))\,dt,\qquad V(x)=\inf_{\pi\in\Pi}C(x,\pi).
--   $$
--
--   **HJB equation** (41)–(42). With $H(x,p)=\inf_{u\in\mathbb S^k}[b(x,u)\cdot p+L(x,u)]$ and $\mathcal L=\tfrac12\sum_ir_i^2\partial^2/\partial x_i^2$, a $C^2$ function $f$ solves (41) if $\mathcal Lf+H(x,Df)-\gamma f=0$ everywhere on $\mathbb R^k$. $C^2_{\mathrm{pol}}$ adds polynomial growth $|f(x)|\le C(1+\|x\|^m)$, and $C^{2,\varrho}_{\mathrm{pol}}$ adds $\varrho$-Hölder continuity of all derivatives of order at most two, uniformly on compact sets.
--
--   These objects are the limiting control problem against which the queueing policies are compared.
--
--   **Formalization Note** The sample space of an admissible system is any `Ω : Type` (universe 0). "Complete filtered" is read as: $P$ complete and every $P$-null set in $\mathcal F_0$. Time is $\mathbb R_{\ge0}$, and time integrals are taken over real $s\in[0,t]$. Costs and $V$ live in $[0,\infty]$ (lower Lebesgue integrals of $e^{-\gamma t}L\ge0$). $V$ is the infimum over systems *and* their controlled processes, which by Proposition 2 is the paper's $V$. Each Brownian coordinate is Mathlib's `IsBrownianReal`; the coordinates are independent, $W$ is adapted, and its increments after $s$ are independent of $\mathcal F_s$. $H$ is a real infimum over the compact simplex; it is meaningful because every statement assumes $k\ge1$ and continuity of $L$. The diffusion data are a free structure; for the queueing model they are computed from the system sequence (`SystemSequence.diffData`).
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), pp. 7-8 (notation), p. 15 (21), p. 16 Assumption 2 and (26), pp. 16-17 Definition 4 and (27), p. 17 C and V, p. 27 (41)-(42)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-!
Atar, Mandelbaum & Reiman (2004), §1.4 (pp. 7–8), §2.4–§2.5 (pp. 15–17) and §3.3 (p. 27): the
diffusion control problem of the multi-class many-server queue in the QED regime.

Conventions. Classes are `Fin k` (paper class `i` is index `i − 1`). Vectors of `ℝ^k` are
`Fin k → ℝ`, and the paper's norm is the ℓ¹ norm `‖x‖ = ∑ᵢ |xᵢ|` (p. 7), written `l1norm`. The
simplex `𝕊^k = {x ∈ ℝ^k_+ : ∑ xᵢ = 1}` is Mathlib's `stdSimplex ℝ (Fin k)`. Time of the diffusion is
`ℝ≥0`; time integrals are taken over real `s ∈ [0, t]` through `Real.toNNReal`.
-/

/-- The ℓ¹ norm `‖x‖ = ∑ᵢ |xᵢ|` of §1.4 (p. 7). -/
def l1norm {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ i, |x i|

/-- The data of the limiting diffusion (16), (25)–(26) (p. 15–16): the drift constants
`ℓ = (ℓᵢ)`, the service rates `µᵢ ∈ (0, ∞)`, the abandonment rates `θᵢ ∈ [0, ∞)` and the
diffusion coefficients `rᵢ`. For the queueing model `ℓᵢ = λ̂ᵢ − ρᵢµ̂ᵢ` (p. 15) and
`rᵢ = (λᵢC²_{U,i} + λᵢ)^{1/2} > 0` (14); see `SystemSequence.diffData`. -/
structure DiffusionData (k : ℕ) where
  /-- `ℓ = (ℓ₁, …, ℓ_k)′` -/
  ell : Fin k → ℝ
  /-- `µ = diag(µᵢ)` -/
  mu : Fin k → ℝ
  /-- `θ = diag(θᵢ)` -/
  theta : Fin k → ℝ
  /-- `r = diag(rᵢ)` -/
  r : Fin k → ℝ
  mu_pos : ∀ i, 0 < mu i
  theta_nonneg : ∀ i, 0 ≤ theta i
  r_pos : ∀ i, 0 < r i

/-- The drift (26) (p. 16): `b(X, u) = ℓ + (µ − θ)(𝟙 · X)⁺ u − µX`, coordinatewise
`bᵢ(X, u) = ℓᵢ + (µᵢ − θᵢ)(𝟙 · X)⁺ uᵢ − µᵢ Xᵢ`. -/
def drift {k : ℕ} (D : DiffusionData k) (x u : Fin k → ℝ) : Fin k → ℝ :=
  fun i => D.ell i + (D.mu i - D.theta i) * max (∑ j, x j) 0 * u i - D.mu i * x i

/-- The change of variables (21) (p. 15): `L(x, u) = L̃((𝟙 · x)⁺u, x − (𝟙 · x)⁺u)`. -/
def costOfTilde {k : ℕ} (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (x u : Fin k → ℝ) : ℝ :=
  Lt (max (∑ j, x j) 0 • u) (x - max (∑ j, x j) 0 • u)

/-- The hypotheses "`L` is continuous and satisfies Assumption 2(i), (iii) and (iv)" of
Proposition 5 and Theorem 3 (pp. 16, 25, 27), for a running cost `L : ℝ^k × 𝕊^k → ℝ`, with the
Hölder exponent `ϱ` of (iii) and the growth exponent `m_L` of (iv) made explicit:
* `L` is continuous on `ℝ^k × 𝕊^k`;
* (i) `L(x, u) ≥ 0` for `(x, u) ∈ ℝ^k × 𝕊^k`;
* (iii) `ϱ ∈ (0, 1)` and for every compact `A ⊂ ℝ^k` there is `c` (depending only on `A`) with
  `|L(x, u) − L(y, u)| ≤ c‖x − y‖^ϱ` for `u ∈ 𝕊^k`, `x, y ∈ A`;
* (iv) `m_L ≥ 0` and there is `c > 0` with `L(x, u) ≤ c(1 + ‖x‖^{m_L})` for `u ∈ 𝕊^k`, `x ∈ ℝ^k`. -/
structure CostAssumptions {k : ℕ} (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL : ℝ) : Prop where
  cont : ContinuousOn (fun p : (Fin k → ℝ) × (Fin k → ℝ) => L p.1 p.2)
    (Set.univ ×ˢ stdSimplex ℝ (Fin k))
  nonneg : ∀ x u, u ∈ stdSimplex ℝ (Fin k) → 0 ≤ L x u
  rho_pos : 0 < ϱ
  rho_lt_one : ϱ < 1
  holder : ∀ A : Set (Fin k → ℝ), IsCompact A → ∃ c : ℝ, ∀ u ∈ stdSimplex ℝ (Fin k),
    ∀ x ∈ A, ∀ y ∈ A, |L x u - L y u| ≤ c * l1norm (x - y) ^ ϱ
  mL_nonneg : 0 ≤ mL
  growth : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ stdSimplex ℝ (Fin k), ∀ x, L x u ≤ c * (1 + l1norm x ^ mL)

/-- Assumption 2 (p. 16) on the queueing cost `L̃ : ℝ^k × ℝ^k → ℝ`: (ii) `(φ, ψ) ↦ L̃(φ, ψ)` is
continuous, and the induced `L` of (21) satisfies (i), (iii), (iv) (its continuity, the "in
particular" of (ii), is included). -/
structure Assumption2 {k : ℕ} (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL : ℝ) : Prop where
  tilde_cont : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => Lt p.1 p.2)
  cost : CostAssumptions (costOfTilde Lt) ϱ mL

/-- A **standard `k`-dimensional `(F_t)`-Brownian motion** (Definition 4(i)2, p. 17): every
coordinate is a real Brownian motion (Mathlib's `IsBrownianReal`: centred Gaussian
finite-dimensional laws with covariance `min s t`, a.s. continuous paths), the `k` coordinate paths
are independent, `W(t)` is `F_t`-measurable, and the increments `W(s + ·) − W(s)` after `s` are
independent of `F_s`. -/
structure IsStdFBrownian {k : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → Fin k → ℝ) : Prop where
  brownian : ∀ i, IsBrownianReal (fun t ω => W t ω i) P
  indep_coord : iIndepFun (fun i ω (t : ℝ≥0) => W t ω i) P
  adapted : ∀ t, Measurable[F t] (W t)
  indep_incr : ∀ s : ℝ≥0,
    Indep (MeasurableSpace.comap (fun ω (t : ℝ≥0) => W (s + t) ω - W s ω) inferInstance) (F s) P

/-- An **admissible system** `π = (Ω, F, (F_t), P, u, W)` (Definition 4(i), p. 16–17):
1. `(Ω, F, (F_t), P)` is a complete filtered probability space: `P` is a complete probability
   measure on `F`, and `(F_t)` is a filtration of `F` whose `F_0` (hence every `F_t`) contains
   all `P`-null sets;
2. `u` is an `𝕊^k`-valued, `F`-measurable, `(F_t)`-progressively measurable process, and `W` is a
   standard `k`-dimensional `(F_t)`-Brownian motion.

The sample space is any `Ω : Type` (universe 0); the class `Π` of all admissible systems is the
type `AdmissibleSystem k`. -/
structure AdmissibleSystem (k : ℕ) where
  /-- the sample space -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- the probability measure -/
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  complete : P.IsComplete
  /-- the filtration `(F_t)` -/
  F : Filtration ℝ≥0 mΩ
  null_mem : ∀ s : Set Ω, P s = 0 → MeasurableSet[F 0] s
  /-- the control `u` -/
  u : ℝ≥0 → Ω → Fin k → ℝ
  u_mem : ∀ t ω, u t ω ∈ stdSimplex ℝ (Fin k)
  u_prog : IsStronglyProgressive F u
  /-- the driving Brownian motion `W` -/
  W : ℝ≥0 → Ω → Fin k → ℝ
  W_bm : IsStdFBrownian P F W

attribute [instance] AdmissibleSystem.mΩ

/-- A **controlled process** associated with initial data `x ∈ ℝ^k` and an admissible system `π`
(Definition 4(ii), p. 17):
1. `X` is a continuous process (every path is continuous), `(F_t)`-adapted (hence `F`-measurable);
2. `∫₀ᵗ |b(X(s), u(s))| ds < ∞` for every `t ≥ 0`, `P`-a.s.;
3. (27) `X(t) = x + rW(t) + ∫₀ᵗ b(X(s), u(s)) ds`, `0 ≤ t < ∞`, holds `P`-a.s. -/
structure IsControlledProcess {k : ℕ} (D : DiffusionData k) (π : AdmissibleSystem k)
    (x : Fin k → ℝ) (X : ℝ≥0 → π.Ω → Fin k → ℝ) : Prop where
  cont : ∀ ω, Continuous (fun t => X t ω)
  adapted : ∀ t, Measurable[π.F t] (X t)
  integrable : ∀ᵐ ω ∂π.P, ∀ t : ℝ, 0 ≤ t →
    IntegrableOn (fun s : ℝ => drift D (X s.toNNReal ω) (π.u s.toNNReal ω)) (Set.Icc 0 t)
  eq27 : ∀ᵐ ω ∂π.P, ∀ t : ℝ≥0,
    X t ω = x + (fun i => D.r i * π.W t ω i) +
      ∫ s in (0 : ℝ)..(t : ℝ), drift D (X s.toNNReal ω) (π.u s.toNNReal ω)

/-- The cost `C(x, π) = E^π_x ∫₀^∞ e^{−γt} L(X(t), u(t)) dt` (p. 17, p. 25) of an admissible system
`π` with controlled process `X`, an iterated lower Lebesgue integral in `[0, ∞]` (the integrand is
nonnegative under Assumption 2(i), so `ENNReal.ofReal` loses nothing). -/
noncomputable def diffCost {k : ℕ} (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (π : AdmissibleSystem k) (X : ℝ≥0 → π.Ω → Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in Set.Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-γ * t) * L (X t.toNNReal ω) (π.u t.toNNReal ω)) ∂volume ∂π.P

/-- The value function `V(x) = inf_{π ∈ Π} C(x, π)` (p. 17), in `[0, ∞]`: the infimum over all
admissible systems `π` and all controlled processes `X` associated with `x` and `π`
(Proposition 2 makes `X` unique up to indistinguishability, so this is the paper's `V`). -/
noncomputable def value {k : ℕ} (D : DiffusionData k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ : ℝ) (x : Fin k → ℝ) : ℝ≥0∞ :=
  ⨅ (π : AdmissibleSystem k) (X : ℝ≥0 → π.Ω → Fin k → ℝ) (_ : IsControlledProcess D π x X),
    diffCost L γ π X

/-- The Hamiltonian `H(x, p) = inf_{u ∈ 𝕊^k} [b(x, u) · p + L(x, u)]` (p. 27). For `k ≥ 1` and `L`
continuous on `ℝ^k × 𝕊^k` the infimum is that of a continuous function on a nonempty compact set,
hence attained; every statement using `H` assumes both. -/
noncomputable def hamiltonian {k : ℕ} (D : DiffusionData k)
    (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (x p : Fin k → ℝ) : ℝ :=
  ⨅ u : stdSimplex ℝ (Fin k), (∑ i, drift D x u i * p i + L x u)

/-- The gradient `Df(x) = (∂f/∂x₁(x), …, ∂f/∂x_k(x))`. -/
noncomputable def grad {k : ℕ} (f : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

/-- `f` is a **solution to the HJB equation (41)** (p. 27): `f` is of class `C²` and
`𝓛f + H(x, Df) − γf = 0` everywhere in `ℝ^k`, where `𝓛 = (1/2)∑ᵢ rᵢ² ∂²/∂xᵢ²`. -/
def IsHJBSolution {k : ℕ} (D : DiffusionData k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (f : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ x,
    (1 / 2) * ∑ i, D.r i ^ 2 * iteratedFDeriv ℝ 2 f x (fun _ => Pi.single i 1) +
      hamiltonian D L x (grad f x) - γ * f x = 0

/-- The polynomial growth condition (42) (p. 27) and of `C_pol` (p. 8): there are `C` and `m` with
`|f(x)| ≤ C(1 + ‖x‖^m)` for all `x ∈ ℝ^k`. -/
def HasPolyGrowth {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ C : ℝ, ∃ m : ℕ, ∀ x, |f x| ≤ C * (1 + l1norm x ^ m)

/-- `f ∈ C²_pol(ℝ^k)` (p. 8): `f` is of class `C²` and has polynomial growth. -/
def IsC2Pol {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasPolyGrowth f

/-- `f ∈ C^{2,ϱ}_pol(ℝ^k)` (p. 8): `f ∈ C²_pol(ℝ^k)` and all derivatives of `f` of order `0, 1, 2`
are `ϱ`-Hölder continuous uniformly on each compact subset of `ℝ^k` (the constant may depend on
the compact set). -/
def IsC2RhoPol {k : ℕ} (ϱ : ℝ) (f : (Fin k → ℝ) → ℝ) : Prop :=
  IsC2Pol f ∧ ∀ A : Set (Fin k → ℝ), IsCompact A → ∃ C : ℝ≥0, ∀ j : ℕ, j ≤ 2 →
    HolderOnWith C ϱ.toNNReal (iteratedFDeriv ℝ j f) A

end ManyServerQED.Scheduling


