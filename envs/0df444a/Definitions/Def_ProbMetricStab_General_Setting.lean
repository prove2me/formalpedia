-- Prove2me | Definitions.Def_ProbMetricStab_General_Setting
-- name    : ProbMetricStab_General_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:28.163548+00:00
-- url     : https://prove2.me/theorems/b6dc04d7-3325-4b2a-9b2e-e4a748892903
-- title:
--   §1–§2, pp. 2–8 — model (1), normal integrands, P_{F_U}, d_{F_U}, M_U, v_U, S_U, metric regularity, CLM sets, Berge usc, ψ, ψ⁻¹, Ψ
-- statement:
--   This file fixes the model (1) of Rachev and Römisch and every object in terms of which Section 2 of the paper is stated.
--
--   **Model.** Let $X\subseteq\mathbb R^m$ be a set of deterministic constraints, $\Xi\subseteq\mathbb R^s$ a set carrying the random data, and $f_j:\Xi\times\mathbb R^m\to\overline{\mathbb R}$, $j=0,\dots,d$, extended-real integrands; $f_0$ is the objective integrand and $f_1,\dots,f_d$ are the constraint integrands. For a Borel probability measure $\nu$ on $\Xi$ the stochastic program is
--   $$\min\Big\{\int_\Xi f_0(\xi,x)\,\nu(d\xi)\ :\ x\in X,\ \int_\Xi f_j(\xi,x)\,\nu(d\xi)\le 0,\ j=1,\dots,d\Big\}.$$
--
--   1. **Normal integrand.** $g:\Xi\times\mathbb R^m\to\overline{\mathbb R}$ is a normal integrand if every epigraph $\operatorname{epi} g(\xi,\cdot)=\{(x,r)\in\mathbb R^m\times\mathbb R: g(\xi,x)\le r\}$ is closed and, for every open $O\subseteq\mathbb R^m\times\mathbb R$, the set $\{\xi:\operatorname{epi} g(\xi,\cdot)\cap O\neq\emptyset\}$ is measurable.
--   2. **General assumptions** (p. 2): $X$ is nonempty and closed, $\Xi$ is closed, and $f_0,\dots,f_d$ are normal integrands. $\mathcal P(\Xi)$ is the set of Borel probability measures on $\Xi$.
--   3. **Feasible set, value, solutions:** $M(\nu)=\{x\in X:\int f_j(\xi,x)\nu(d\xi)\le0,\ j=1,\dots,d\}$, $v(\nu)=\inf\{\int f_0(\xi,x)\nu(d\xi):x\in M(\nu)\}$, $S(\nu)=\{x\in M(\nu):\int f_0(\xi,x)\nu(d\xi)=v(\nu)\}$.
--   4. **Measures and distance** (p. 4). For a nonempty $\mathcal U\subseteq\mathbb R^m$, $\mathcal P_{\mathcal F_{\mathcal U}}$ is the set of $\nu\in\mathcal P(\Xi)$ such that, for each $j=0,\dots,d$,
--   $$-\infty<\int_\Xi\inf_{x\in X,\ \|x\|\le r}f_j(\xi,x)\,\nu(d\xi)\ \text{ for each } r>0,\qquad \sup_{x\in X\cap\operatorname{cl}\mathcal U}\int_\Xi f_j(\xi,x)\,\nu(d\xi)<\infty,$$
--   and the minimal information distance is
--   $$d_{\mathcal F_{\mathcal U}}(\mu,\nu)=\sup_{x\in X\cap\operatorname{cl}\mathcal U}\ \max_{j=0,\dots,d}\Big|\int_\Xi f_j(\xi,x)\,\mu(d\xi)-\int_\Xi f_j(\xi,x)\,\nu(d\xi)\Big|\in[0,\infty].$$
--   5. **Localized problem** (pp. 4–5): $M_{\mathcal U}(\nu)=M(\nu)\cap\operatorname{cl}\mathcal U$, $v_{\mathcal U}(\nu)=\inf\{\int f_0(\xi,x)\nu(d\xi):x\in M_{\mathcal U}(\nu)\}$, $S_{\mathcal U}(\nu)=\{x\in M_{\mathcal U}(\nu):\int f_0(\xi,x)\nu(d\xi)=v_{\mathcal U}(\nu)\}$.
--   6. **Metric regularity** (p. 5). With $M_y(\mu)=\{x\in X:\int f_j(\xi,x)\mu(d\xi)\le y_j,\ j=1,\dots,d\}$ for $y\in\mathbb R^d$, the inverse $x\mapsto M^{-1}_x(\mu)$ is metrically regular at $(\bar x,0)$ if there are $a\ge0$ and $\varepsilon>0$ such that for all $x\in X\cap\mathbb B(\bar x,\varepsilon)$ and all $y$ with $\max_j|y_j|\le\varepsilon$,
--   $$d\big(x,M_y(\mu)\big)\le a\max_{j=1,\dots,d}\max\Big\{0,\int_\Xi f_j(\xi,x)\,\mu(d\xi)-y_j\Big\}.$$
--   7. **CLM set** (p. 6): a nonempty $\mathcal S$ is a complete local minimizing set of the perturbed problem with respect to $\mathcal U$ if $\mathcal U$ is open and $\mathcal S=S_{\mathcal U}(\nu)\subseteq\mathcal U$.
--   8. **Berge upper semicontinuity** of $S_{\mathcal U}$ at $\mu$: for every open $O\supseteq S_{\mathcal U}(\mu)$ there is $\varepsilon>0$ with $S_{\mathcal U}(\nu)\subseteq O$ for all $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$ with $d_{\mathcal F_{\mathcal U}}(\mu,\nu)<\varepsilon$.
--   9. **Growth function** (p. 8): for $\tau\ge0$,
--   $$\psi(\tau)=\inf\Big\{\int_\Xi f_0(\xi,x)\,\mu(d\xi)-v(\mu)\ :\ d(x,S(\mu))\ge\tau,\ x\in M_{\mathcal U}(\mu)\Big\},$$
--   $\psi^{-1}(t)=\sup\{\tau\ge0:\psi(\tau)\le t\}$ and $\Psi(\eta)=\eta+\psi^{-1}(\eta)$.
--   10. **Assumptions of Theorem 2.2** (p. 6): the general assumptions, $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, and (i) $S(\mu)\neq\emptyset$ and $\mathcal U$ is an open bounded neighbourhood of $S(\mu)$; (ii) if $d\ge1$, $x\mapsto\int f_0(\xi,x)\mu(d\xi)$ is Lipschitz continuous on $X\cap\operatorname{cl}\mathcal U$; (iii) metric regularity at $(\bar x,0)$ for every $\bar x\in S(\mu)$.
--   11. $A+r\mathbb B=\{x:\exists a\in A,\ \|x-a\|\le r\}$ for $r\in[0,\infty]$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)` (the paper never fixes its norm; every statement holds for any norm with existential constants). The integrands are indexed by `Fin (d+1)`: `f 0` is $f_0$ and `f i.succ` ($i:$ `Fin d`) is the paper's $f_{i+1}$. Measures live on the subtype $\Xi$ with its subspace Borel σ-algebra. Every integral of an extended-real integrand is the published `DupacovaWets.Consistency.expect` ($+\infty$ when $\int f^+=\infty$, else $\int f^+-\int f^-$). The value functions $v,v_{\mathcal U}$ and $\psi$ are infima in $\overline{\mathbb R}$ ($+\infty$ on the empty set; the paper's "min" in $\psi$ is read as an infimum). $d(x,A)$ is the extended distance `Metric.infEDist` ($=\infty$ for $A=\emptyset$), and $\psi^{-1}$, $\Psi$, $d_{\mathcal F_{\mathcal U}}$ take values in $[0,\infty]$. $|a-b|$ for extended reals is `EReal.abs`; on $\mathcal P_{\mathcal F_{\mathcal U}}$ every integral at $x\in X\cap\operatorname{cl}\mathcal U$ is finite. In metric regularity $\max\{0,t\}$ is `t.toENNReal`, the maximum over an empty index set ($d=0$) is $0$, and $a\cdot\infty$ follows the convention $0\cdot\infty=0$. $\mathbb B(\bar x,\varepsilon)$ is the closed ball. Lipschitz continuity in (ii) is stated for the real-valued function $x\mapsto\int f_0(\xi,x)\mu(d\xi)$ on $X\cap\operatorname{cl}\mathcal U$, where this integral is finite.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), pp. 2–8, (1), (3), Section 2 (definitions of F_U, M_U, P_{F_U}, d_{F_U}, M_y, metric regularity, v_U, S_U, CLM set, Theorem 2.2 (i)–(iii), ψ, ψ⁻¹, Ψ of Theorem 2.3)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
open MeasureTheory Set Metric
open scoped ENNReal

namespace ProbMetricStab.General

/-- Rachev–Römisch, p. 2: `g : Ω × ℝ^m → ℝ̄` is a *normal integrand* if its epigraphical mapping
`ω ↦ epi g(ω, ·) = {(x, r) ∈ ℝ^m × ℝ : g(ω, x) ≤ r}` is closed-valued and measurable, i.e. every
epigraph is closed and, for every open `O ⊆ ℝ^m × ℝ`, the set `{ω | epi g(ω, ·) ∩ O ≠ ∅}` is
measurable (Rockafellar–Wets, Def. 14.1 and 14.27). -/
def IsNormalIntegrand {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → EuclideanSpace ℝ (Fin m) → EReal) : Prop :=
  (∀ ω, IsClosed {p : EuclideanSpace ℝ (Fin m) × ℝ | g ω p.1 ≤ (p.2 : EReal)}) ∧
  ∀ O : Set (EuclideanSpace ℝ (Fin m) × ℝ), IsOpen O →
    MeasurableSet {ω | ({p : EuclideanSpace ℝ (Fin m) × ℝ | g ω p.1 ≤ (p.2 : EReal)} ∩ O).Nonempty}

/-- The data of model (1), p. 2: the deterministic constraint set `X ⊆ ℝ^m`, the closed support
set `Ξ ⊆ ℝ^s`, and the integrands `f j : Ξ × ℝ^m → ℝ̄` for `j = 0, …, d`, where `f 0` is the
objective integrand and `f (i+1)` (`i : Fin d`) is the paper's constraint integrand `f_{i+1}`. -/
structure Model (m s d : ℕ) where
  X : Set (EuclideanSpace ℝ (Fin m))
  Ξ : Set (EuclideanSpace ℝ (Fin s))
  f : Fin (d + 1) → ↥Ξ → EuclideanSpace ℝ (Fin m) → EReal

namespace Model

variable {m s d : ℕ} (P : Model m s d)

/-- The general assumptions of Section 1 (p. 2) on `X`, `Ξ` and the `f_j`: `X` is nonempty and
closed, `Ξ` is closed, and every `f_j` (`j = 0, …, d`) is a normal integrand. -/
structure GeneralAssumptions : Prop where
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  Ξ_closed : IsClosed P.Ξ
  normal : ∀ j, IsNormalIntegrand (P.f j)

/-- `𝒫(Ξ)`: the Borel probability measures on `Ξ` (p. 2). -/
def ProbMeasures : Set (Measure ↥P.Ξ) := {ν | IsProbabilityMeasure ν}

/-- `∫_Ξ f_j(ξ, x) ν(dξ)`, the extended-real expectation (`+∞` when `∫ f_j⁺ = ∞`). -/
noncomputable def integral (ν : Measure ↥P.Ξ) (j : Fin (d + 1))
    (x : EuclideanSpace ℝ (Fin m)) : EReal :=
  DupacovaWets.Consistency.expect ν (fun ξ => P.f j ξ x)

/-- `M(ν) = {x ∈ X : ∫ f_j(ξ, x) ν(dξ) ≤ 0, j = 1, …, d}` (p. 2). -/
def M (ν : Measure ↥P.Ξ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ P.X ∧ ∀ i : Fin d, P.integral ν i.succ x ≤ 0}

/-- `v(ν) = inf {∫ f_0(ξ, x) ν(dξ) : x ∈ M(ν)}` (p. 2), `+∞` on an empty feasible set. -/
noncomputable def v (ν : Measure ↥P.Ξ) : EReal :=
  ⨅ x ∈ P.M ν, P.integral ν 0 x

/-- `S(ν) = {x ∈ M(ν) : ∫ f_0(ξ, x) ν(dξ) = v(ν)}` (p. 2). -/
def S (ν : Measure ↥P.Ξ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ P.M ν ∧ P.integral ν 0 x = P.v ν}

/-- `𝒫_{ℱ_𝒰}(Ξ)` (p. 4): Borel probability measures `ν` on `Ξ` with
`-∞ < ∫ inf_{x ∈ X, ‖x‖ ≤ r} f_j(ξ, x) ν(dξ)` for each `r > 0` and
`sup_{x ∈ X ∩ cl 𝒰} ∫ f_j(ξ, x) ν(dξ) < ∞`, for each `j = 0, …, d`. -/
def PFU (U : Set (EuclideanSpace ℝ (Fin m))) : Set (Measure ↥P.Ξ) :=
  {ν | IsProbabilityMeasure ν ∧ ∀ j : Fin (d + 1),
    (∀ r : ℝ, 0 < r →
      ⊥ < DupacovaWets.Consistency.expect ν
        (fun ξ => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) | x ∈ P.X ∧ ‖x‖ ≤ r}, P.f j ξ x)) ∧
    (⨆ x ∈ P.X ∩ closure U, P.integral ν j x) < ⊤}

/-- The probability distance `d_{ℱ_𝒰}(μ, ν) = sup_{x ∈ X ∩ cl 𝒰} max_{j = 0, …, d}
|∫ f_j(ξ, x)(μ − ν)(dξ)|` (p. 4), valued in `[0, ∞]`. -/
noncomputable def dFU (U : Set (EuclideanSpace ℝ (Fin m))) (μ ν : Measure ↥P.Ξ) : ℝ≥0∞ :=
  ⨆ x ∈ P.X ∩ closure U, ⨆ j : Fin (d + 1), EReal.abs (P.integral μ j x - P.integral ν j x)

/-- `M_𝒰(ν) = {x ∈ X ∩ cl 𝒰 : ∫ f_j(ξ, x) ν(dξ) ≤ 0, j = 1, …, d}` (p. 4). -/
def MU (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥P.Ξ) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ P.X ∩ closure U ∧ ∀ i : Fin d, P.integral ν i.succ x ≤ 0}

/-- `v_𝒰(ν) = inf {∫ f_0(ξ, x) ν(dξ) : x ∈ M_𝒰(ν)}` (p. 5). -/
noncomputable def vU (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥P.Ξ) : EReal :=
  ⨅ x ∈ P.MU U ν, P.integral ν 0 x

/-- `S_𝒰(ν) = {x ∈ M_𝒰(ν) : ∫ f_0(ξ, x) ν(dξ) = v_𝒰(ν)}` (p. 5). -/
def SU (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥P.Ξ) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ P.MU U ν ∧ P.integral ν 0 x = P.vU U ν}

/-- `M_y(μ) = {x ∈ X : ∫ f_j(ξ, x) μ(dξ) ≤ y_j, j = 1, …, d}` for `y ∈ ℝ^d` (p. 5). -/
def My (μ : Measure ↥P.Ξ) (y : Fin d → ℝ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | x ∈ P.X ∧ ∀ i : Fin d, P.integral μ i.succ x ≤ (y i : EReal)}

/-- The metric-regularity estimate of p. 5 with constants `a` and `ε`: for all
`x ∈ X ∩ 𝔹(x̄, ε)` and `y ∈ ℝ^d` with `max_j |y_j| ≤ ε`,
`d(x, M_y(μ)) ≤ a · max_{j = 1, …, d} max{0, ∫ f_j(ξ, x) μ(dξ) − y_j}`.
The distance is `infEDist` (`= ∞` to the empty set); the maximum over the empty index set
(`d = 0`) is `0`; `max{0, t}` is `t.toENNReal`. -/
def MetricRegularityEstimate (μ : Measure ↥P.Ξ) (xbar : EuclideanSpace ℝ (Fin m))
    (a ε : ℝ) : Prop :=
  ∀ x ∈ P.X ∩ closedBall xbar ε, ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ ε) →
    infEDist x (P.My μ y) ≤
      ENNReal.ofReal a * ⨆ i : Fin d, (P.integral μ i.succ x - (y i : EReal)).toENNReal

/-- The inverse `x ↦ M_x^{-1}(μ)` is *metrically regular* at `(x̄, 0)` (p. 5): there are
constants `a ≥ 0` and `ε > 0` with the metric-regularity estimate. -/
def IsMetricallyRegularAt (μ : Measure ↥P.Ξ) (xbar : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∃ a ε : ℝ, 0 ≤ a ∧ 0 < ε ∧ P.MetricRegularityEstimate μ xbar a ε

/-- A nonempty set `𝒮 ⊆ ℝ^m` is a *complete local minimizing (CLM) set* of (3) with respect to
`𝒰` (p. 6) if `𝒰` is open and `𝒮 = S_𝒰(ν) ⊂ 𝒰`. -/
def IsCLMSet (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥P.Ξ)
    (T : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  T.Nonempty ∧ IsOpen U ∧ T = P.SU U ν ∧ T ⊆ U

/-- `S_𝒰` from `(𝒫_{ℱ_𝒰}, d_{ℱ_𝒰})` to `ℝ^m` is (Berge) upper semicontinuous at `μ`: for
every open `O ⊇ S_𝒰(μ)` there is `ε > 0` with `S_𝒰(ν) ⊆ O` for all `ν ∈ 𝒫_{ℱ_𝒰}` with
`d_{ℱ_𝒰}(μ, ν) < ε`. -/
def SUIsBergeUSCAt (U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure ↥P.Ξ) : Prop :=
  ∀ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O → P.SU U μ ⊆ O →
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ P.PFU U, P.dFU U μ ν < ENNReal.ofReal ε → P.SU U ν ⊆ O

/-- The growth function of p. 8, `ψ(τ) = min {∫ f_0(ξ, x) μ(dξ) − v(μ) : d(x, S(μ)) ≥ τ,
x ∈ M_𝒰(μ)}` (`τ ∈ ℝ₊`), read as an infimum in `ℝ̄` (`+∞` when no feasible point is
`τ`-far from `S(μ)`). -/
noncomputable def ψ (U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure ↥P.Ξ) (τ : ℝ) : EReal :=
  ⨅ x ∈ {x | x ∈ P.MU U μ ∧ ENNReal.ofReal τ ≤ infEDist x (P.S μ)},
    (P.integral μ 0 x - P.v μ)

/-- `ψ^{-1}(t) = sup {τ ∈ ℝ₊ : ψ(τ) ≤ t}` (p. 8), a supremum in `[0, ∞]`. -/
noncomputable def ψinv (U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure ↥P.Ξ) (t : EReal) :
    ℝ≥0∞ :=
  ⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ P.ψ U μ τ ≤ t}, ENNReal.ofReal τ

/-- `Ψ(η) = η + ψ^{-1}(η)` (Theorem 2.3, p. 8), for `η ∈ [0, ∞]`. -/
noncomputable def Ψ (U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure ↥P.Ξ) (η : ℝ≥0∞) :
    ℝ≥0∞ :=
  η + P.ψinv U μ (η : EReal)

/-- The assumptions of Theorem 2.2 (p. 6): the general assumptions, `μ ∈ 𝒫_{ℱ_𝒰}`, and
(i) `S(μ)` is nonempty and `𝒰` is an open bounded neighbourhood of `S(μ)`;
(ii) if `d ≥ 1`, `x ↦ ∫ f_0(ξ, x) μ(dξ)` is Lipschitz continuous on `X ∩ cl 𝒰`;
(iii) `x ↦ M_x^{-1}(μ)` is metrically regular at each `(x̄, 0)` with `x̄ ∈ S(μ)`. -/
structure Thm22Assumptions (U : Set (EuclideanSpace ℝ (Fin m))) (μ : Measure ↥P.Ξ) : Prop where
  general : P.GeneralAssumptions
  mem_PFU : μ ∈ P.PFU U
  S_nonempty : (P.S μ).Nonempty
  U_open : IsOpen U
  U_bounded : Bornology.IsBounded U
  S_subset_U : P.S μ ⊆ U
  lipschitz : 1 ≤ d → ∃ K : NNReal,
    LipschitzOnWith K (fun x => (P.integral μ 0 x).toReal) (P.X ∩ closure U)
  regular : ∀ xbar ∈ P.S μ, P.IsMetricallyRegularAt μ xbar

end Model

/-- `A + r𝔹 = {x : ∃ a ∈ A, ‖x − a‖ ≤ r}` for `r ∈ [0, ∞]` (`𝔹` the closed unit ball). -/
def enlarge {m : ℕ} (A : Set (EuclideanSpace ℝ (Fin m))) (r : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∃ a ∈ A, edist x a ≤ r}

end ProbMetricStab.General


