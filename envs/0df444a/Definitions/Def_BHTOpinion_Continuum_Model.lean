-- Prove2me | Definitions.Def_BHTOpinion_Continuum_Model
-- name    : BHTOpinion_Continuum_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:11.21124+00:00
-- url     : https://prove2.me/theorems/b94a3b48-932d-4a49-a1d1-9a0d3cbd776c
-- title:
--   The continuum opinion model of Section 3: Y, X, X_m, X^M, regular functions, the operator 𝓛 (3.3), solutions of (3.1)–(3.2), F, F̄, fixed points, clusters
-- statement:
--   This file sets up the continuum-agent opinion model of Blondel, Hendrickx and Tsitsiklis (Section 3).
--
--   **Agents and opinion functions.** The agents are indexed by $I=[0,1]$ with Lebesgue measure. An opinion function $\tilde x$ assigns an opinion $\tilde x(\alpha)\in\mathbb R$ to every agent $\alpha\in I$.
--
--   1. $Y$ is the set of bounded measurable functions $\tilde x : I\to\mathbb R$.
--   2. $X$ is the set of nondecreasing bounded functions $\tilde x : I\to\mathbb R$.
--   3. For $m,M>0$, $X_m$ is the set of $\tilde x\in X$ with $\frac{\tilde x(\beta)-\tilde x(\alpha)}{\beta-\alpha}\ge m$ for all $\beta\ne\alpha$ in $I$, and $X^M$ the set of $\tilde x\in X$ with this quotient $\le M$. A function is **regular** if it belongs to $X_m^M=X_m\cap X^M$ for some $m,M>0$.
--
--   **The interaction operator.** Two agents $\alpha,\gamma$ are connected under $\tilde x$ when $|\tilde x(\alpha)-\tilde x(\gamma)|<1$; $C_{\tilde x}\subseteq I^2$ is the set of connected pairs and $\chi_{\tilde x}$ its indicator. The operator $\mathcal L$ of (3.3) is
--
--   $$\mathcal L(\tilde x)(\alpha)=\int_0^1 \chi_{\tilde x}(\alpha,\gamma)\,\bigl(\tilde x(\gamma)-\tilde x(\alpha)\bigr)\,d\gamma .$$
--
--   **The dynamics.** Given an initial opinion function $\tilde x_0$, a **solution of the integral equation (3.2)** is a measurable function $x : I\times[0,\infty)\to\mathbb R$, $(\alpha,t)\mapsto x_t(\alpha)$, with every $x_t\in Y$, such that for every $t\ge 0$ and every $\alpha\in I$
--
--   $$x_t(\alpha)=\tilde x_0(\alpha)+\int_0^t \mathcal L(x_\tau)(\alpha)\,d\tau .$$
--
--   A **solution of the differential equation (3.1)** is a function with every $x_t\in Y$, $x_0=\tilde x_0$ on $I$, and $\frac{d}{dt}x_t(\alpha)=\mathcal L(x_t)(\alpha)$ for every $\alpha\in I$ and $t\ge0$ (a right derivative at $t=0$).
--
--   **Equilibria.** $F$ is the set of nondecreasing bounded $\tilde s$ such that for every $\alpha,\beta\in I$ either $\tilde s(\alpha)=\tilde s(\beta)$ or $|\tilde s(\alpha)-\tilde s(\beta)|>1$. $\bar F$ is the set of nondecreasing bounded $\tilde s$ such that for almost every pair $(\alpha,\beta)\in I^2$ (two-dimensional Lebesgue measure) either $\tilde s(\alpha)=\tilde s(\beta)$ or $|\tilde s(\alpha)-\tilde s(\beta)|\ge 1$. A function $\tilde s\in X$ is a **fixed point** if (3.2) with initial condition $\tilde s$ has a unique solution and that solution is $x_t=\tilde s$ for all $t$.
--
--   **Clusters.** For a function $\tilde s$ and a value $A$, the **weight** $W_A$ is the Lebesgue measure of $\{\alpha\in I:\tilde s(\alpha)=A\}$; $A$ is a **cluster** of $\tilde s$ if $W_A>0$.
--
--   These objects are shared by every statement of the mission: the Lipschitz and rate bounds on $\mathcal L$, existence and uniqueness of solutions, convergence to $\bar F$, and the intercluster distance bound.
--
--   **Formalization Note** Opinion functions are typed $\mathbb R\to\mathbb R$ and only their values on $I=[0,1]$ enter any definition; $x_t(\alpha)$ is `x t α` with time first. The slope conditions are written multiplied out, $m(\beta-\alpha)\le \tilde x(\beta)-\tilde x(\alpha)$ for $\alpha<\beta$, which is the paper's quotient condition without division. The page prints "$|\tilde s(\alpha)-s(\beta)|$" in the definitions of $F$ and $\bar F$; it is read as $|\tilde s(\alpha)-\tilde s(\beta)|$. The paper writes (3.2) without saying the time integral exists; the solution predicate requires $\tau\mapsto\mathcal L(x_\tau)(\alpha)$ to be integrable on $[0,t]$ (implicit well-posedness, since a Lean integral of a non-integrable function is $0$). Measurability of $x$ is joint, on $I\times[0,\infty)$, as on p. 5222. The weight $W_A$ is defined as a measure; the paper calls it "the length of the interval $\tilde s^{-1}(A)$", which coincides for nondecreasing $\tilde s$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), pp. 5222–5223 (Y, X, (3.1), C_x̃, (3.2), footnote 6, X_m, X^M, regular, (3.3)), p. 5227 (F, F̄, fixed point), p. 5228 (clusters, weights)

import Mathlib

namespace BHTOpinion.Continuum

open MeasureTheory

/-- The set of agents `I = [0, 1]` (p. 5222). Opinion functions are typed `ℝ → ℝ`; only their
values on `I` enter any definition below. -/
abbrev I : Set ℝ := Set.Icc (0 : ℝ) 1

/-- `Y` (p. 5222): bounded measurable opinion functions `I → ℝ`. -/
def InY (x : ℝ → ℝ) : Prop :=
  Measurable (fun a : I => x a) ∧ ∃ C : ℝ, ∀ α ∈ I, |x α| ≤ C

/-- `X` (p. 5222): nondecreasing bounded opinion functions on `I`. -/
def InX (x : ℝ → ℝ) : Prop :=
  MonotoneOn x I ∧ ∃ C : ℝ, ∀ α ∈ I, |x α| ≤ C

/-- `X_m` (p. 5223): `x ∈ X` with `(x β - x α)/(β - α) ≥ m` for all `β ≠ α` in `I`
(written multiplied out for `α < β`). -/
def InXm (m : ℝ) (x : ℝ → ℝ) : Prop :=
  InX x ∧ ∀ α ∈ I, ∀ β ∈ I, α < β → m * (β - α) ≤ x β - x α

/-- `X^M` (p. 5223): `x ∈ X` with `(x β - x α)/(β - α) ≤ M` for all `β ≠ α` in `I`. -/
def InXM (M : ℝ) (x : ℝ → ℝ) : Prop :=
  InX x ∧ ∀ α ∈ I, ∀ β ∈ I, α < β → x β - x α ≤ M * (β - α)

/-- Regular (p. 5223): `x ∈ X_m^M = X_m ∩ X^M` for some `m, M > 0`. -/
def Regular (x : ℝ → ℝ) : Prop :=
  ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ InXm m x ∧ InXM M x

/-- The operator `𝓛` of (3.3) (p. 5223):
`𝓛(x)(α) = ∫_I χ_x(α, γ) (x(γ) - x(α)) dγ`, where `χ_x` is the indicator of the connection set
`C_x = {(α, γ) ∈ I² : |x(α) - x(γ)| < 1}`. -/
noncomputable def opL (x : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ γ in I, if |x α - x γ| < 1 then x γ - x α else 0

/-- A solution of the integral equation (3.2) (p. 5222) with initial opinion function `x0`:
`x t α` is the opinion `x_t(α)` of agent `α ∈ I` at time `t ≥ 0`; `x` is measurable on
`I × [0, ∞)`, every `x_t` lies in `Y`, and for **every** `t ≥ 0` and **every** `α ∈ I`
(footnote 6) `x_t(α) = x0(α) + ∫_0^t 𝓛(x_τ)(α) dτ`, the time integral existing. -/
structure IsSolution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (fun p : I × Set.Ici (0 : ℝ) => x p.2 p.1)
  mem_Y : ∀ t : ℝ, 0 ≤ t → InY (x t)
  integrable : ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I,
    IntervalIntegrable (fun τ => opL (x τ) α) volume 0 t
  eq : ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, x t α = x0 α + ∫ τ in (0 : ℝ)..t, opL (x τ) α

/-- A solution of the differential equation (3.1) (p. 5222) with initial opinion function `x0`:
every `x_t` lies in `Y`, `x_0 = x0` on `I`, and for every `α ∈ I` and `t ≥ 0`,
`d/dt x_t(α) = 𝓛(x_t)(α)` (a right derivative at `t = 0`). -/
structure IsDiffSolution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ) : Prop where
  mem_Y : ∀ t : ℝ, 0 ≤ t → InY (x t)
  init : ∀ α ∈ I, x 0 α = x0 α
  deriv : ∀ α ∈ I, ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun τ => x τ α) (opL (x t) α) (Set.Ici 0) t

/-- `F` (p. 5227): nondecreasing (bounded) `s` such that for every `α, β ∈ I`, either
`s(α) = s(β)` or `|s(α) - s(β)| > 1`. -/
def InF (s : ℝ → ℝ) : Prop :=
  InX s ∧ ∀ α ∈ I, ∀ β ∈ I, s α = s β ∨ 1 < |s α - s β|

/-- `F̄` (p. 5227): nondecreasing (bounded) `s` such that for almost every pair `(α, β) ∈ I²`
(two-dimensional Lebesgue measure), either `s(α) = s(β)` or `|s(α) - s(β)| ≥ 1`. -/
def InFbar (s : ℝ → ℝ) : Prop :=
  InX s ∧ ∀ᵐ p ∂((volume.restrict I).prod (volume.restrict I)),
    s p.1 = s p.2 ∨ 1 ≤ |s p.1 - s p.2|

/-- Fixed point (p. 5227): `s ∈ X` such that (3.2) with initial condition `s` admits a unique
solution, and that solution is `x_t = s` for all `t`. -/
def IsFixedPoint (s : ℝ → ℝ) : Prop :=
  InX s ∧ IsSolution s (fun _ => s) ∧
    ∀ y : ℝ → ℝ → ℝ, IsSolution s y → ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, y t α = s α

/-- The weight `W_A` of the value `A` (p. 5228): the Lebesgue measure of the set of agents
`{α ∈ I : s(α) = A}` holding opinion `A`. -/
noncomputable def weight (s : ℝ → ℝ) (A : ℝ) : ℝ :=
  (volume (I ∩ s ⁻¹' {A})).toReal

/-- A cluster of `s` (p. 5228): a value `A` held by a positive-measure set of agents. -/
def IsCluster (s : ℝ → ℝ) (A : ℝ) : Prop :=
  0 < weight s A

end BHTOpinion.Continuum


