-- Prove2me | Definitions.Def_InfoRelax_IdealPenalty_Framework
-- name    : InfoRelax_IdealPenalty_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:28.822998+00:00
-- url     : https://prove2.me/theorems/4f35dc4f-28e5-4729-aceb-7636f368c881
-- title:
--   Policies, information relaxations, penalties, and the primal and dual values (§2.1–§2.2)
-- statement:
--   This file sets up the general framework of Brown, Smith and Sun for a finite-horizon stochastic dynamic program and its dual.
--
--   Uncertainty is a probability space $(\Omega,\mathcal F,\mathbb P)$. Time is $t=0,\dots,T$, and an **action sequence** is $a=(a_0,\dots,a_T)$ with actions in a measurable space $X$; a set $A$ of action sequences is the **feasible set**. The total reward is a function $r(a,\omega)$. A **filtration** $\mathbb G=(\mathcal G_0,\dots,\mathcal G_T)$ is an increasing family of sub-$\sigma$-algebras of $\mathcal F$.
--
--   1. **Policies.** A policy is a map $\alpha:\Omega\to A$. It is **adapted to $\mathbb G$** if each action $\omega\mapsto\alpha(\omega)_t$ is $\mathcal G_t$-measurable; $\mathcal A_{\mathbb G}$ is the set of such policies. The **perfect-information filtration** $\mathbb I$ has $\mathcal I_t=\mathcal F$ for all $t$, and $\mathcal A=\mathcal A_{\mathbb I}$ is the set of all (measurable) policies.
--   2. **Relaxations.** $\mathbb G$ is a **relaxation** of the natural filtration $\mathbb F$ if $\mathcal F_t\subseteq\mathcal G_t\subseteq\mathcal F$ for every $t$, written $\mathbb F\subseteq\mathbb G$.
--   3. **Penalties.** The penalty set $\mathcal Z$ consists of the functions $z(a,\omega)$ for which $\mathbb E[z(\alpha)]=\mathbb E[z(\alpha(\omega),\omega)]$ exists for every $\alpha\in\mathcal A$. The **dual feasible penalties** are
--   $$\mathcal Z_{\mathbb F}=\{z\in\mathcal Z:\ \mathbb E[z(\alpha_F)]\le 0\ \text{for all }\alpha_F\in\mathcal A_{\mathbb F}\}.\qquad(3)$$
--   4. **Values.** For a set $P$ of policies and a function $f(a,\omega)$, $\sup_{\alpha\in P}\mathbb E[f(\alpha)]$ is taken in the extended reals. The **primal value** (1) is $\sup_{\alpha\in\mathcal A_{\mathbb F}}\mathbb E[r(\alpha)]$; the **dual bound** of a pair $(\mathbb G,z)$, the right side of (4), is $\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)]$; the **dual value** (6) is $\inf_{z\in\mathcal Z_{\mathbb F}}$ of the dual bound.
--   5. **Integrable rewards.** The reward is integrable if $\mathbb E[r(\alpha)]$ exists for every $\alpha\in\mathcal A$.
--
--   These objects carry the weak and strong duality theory of §2.2, which holds for any feasible set and any total reward.
--
--   **Formalization Note** One action type $X$ serves every period (the disjoint union of the page's $A_t$). Adaptedness of each action is equivalent to the page's "the first $t+1$ actions are $\mathcal F_t$-measurable" because filtrations increase. Integrability is the field's standing convention, which the page leaves implicit. Values are in `EReal`, so that an empty set of policies gives $-\infty$ and an unbounded one $+\infty$ rather than a default $0$; the difference $r-z$ is integrated as a real function and never subtracted in `EReal`.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, pp. 2–3, §2.1 (primal DP (1)) and §2.2 (relaxations, penalty set, eq. (3), right side of (4), eq. (6) on p. 4)

import Mathlib

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-!
# The general framework of Brown, Smith & Sun (2010), §2.1–§2.2

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, pp. 2–4:
§2.1 "General Framework" (policies, nonanticipative policies, the primal DP (1)) and
§2.2 "The Dual Approach" (relaxations, the penalty set, dual feasible penalties (3), the dual
bound on the right of (4), the dual problem (6)).

Periods are `t : Fin (T + 1)` (the page's `t = 0, …, T`); an action sequence is
`a : Fin (T + 1) → X`; `A` is the set of feasible action sequences; `r a ω` is the total reward.
A filtration of the ambient σ-algebra `mΩ` (the page's `𝓕`) is a Mathlib `Filtration`, which
already encodes `𝓕_t ⊆ 𝓕_{t+1} ⊆ 𝓕`.

**Formalization Note.**
* One action type `X` for every period (take `X` to be the disjoint union of the page's `A_t`).
* A policy is adapted to `𝔾` when each action `ω ↦ α ω t` is `𝔾 t`-measurable. Because `𝔾` is
  increasing this is equivalent to the page's "the selection of the first `t + 1` actions is
  `𝒢_t`-measurable".
* `𝒜` (`policies`) is the set of policies adapted to the perfect-information filtration, i.e. the
  measurable policies; the page's `𝒜_𝕀 = 𝒜` (p. 3).
* Integrability is the field's standing convention, unstated on the page: a penalty in `𝒵` is
  integrable along every policy of `𝒜`.
* Values are in `EReal` and are suprema/infima over the adapted subsets, so that `+∞` is a value
  and an empty set gives `⊥`/`⊤` rather than a junk `0`. Never an `EReal` subtraction: the
  difference `r - z` is integrated as a real function and then coerced.
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}

/-- The set `𝒜_𝔾` of policies `α : Ω → A` adapted to the filtration `𝔾` (p. 3). -/
def adaptedPolicies (A : Set (Fin (T + 1) → X)) (𝔾 : Filtration (Fin (T + 1)) mΩ) :
    Set (Ω → Fin (T + 1) → X) :=
  {α | (∀ ω, α ω ∈ A) ∧ ∀ t, Measurable[𝔾 t] (fun ω => α ω t)}

/-- The perfect-information filtration `𝕀`, with `𝒥_t = 𝓕` for all `t` (p. 3). -/
def perfectInfo : Filtration (Fin (T + 1)) mΩ :=
  ⊤

/-- The set `𝒜 = 𝒜_𝕀` of all (measurable) policies (p. 3). -/
def policies (A : Set (Fin (T + 1) → X)) : Set (Ω → Fin (T + 1) → X) :=
  adaptedPolicies A (perfectInfo (Ω := Ω) (T := T))

/-- `𝔾` is a relaxation of `𝔽`: `𝓕_t ⊆ 𝒢_t ⊆ 𝓕` for every `t` (p. 3), written `𝔽 ⊆ 𝔾`.
The inclusion `𝒢_t ⊆ 𝓕` is built into `Filtration`. -/
def IsRelaxation (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) : Prop :=
  𝔽 ≤ 𝔾

/-- The set `𝒵` of penalties `z(a, ω)` (p. 3), restricted to those whose expectation along every
policy exists: `ω ↦ z(α(ω), ω)` is integrable for every `α ∈ 𝒜`. -/
def penalties (μ : Measure Ω) (A : Set (Fin (T + 1) → X)) :
    Set ((Fin (T + 1) → X) → Ω → ℝ) :=
  {z | ∀ α ∈ policies (Ω := Ω) A, Integrable (fun ω => z (α ω) ω) μ}

/-- The set `𝒵_𝔽` of dual feasible penalties, eq. (3), p. 3:
`𝒵_𝔽 = {z ∈ 𝒵 : 𝔼[z(α_F)] ≤ 0 for all α_F ∈ 𝒜_𝔽}`. -/
def dualFeasible (μ : Measure Ω) (A : Set (Fin (T + 1) → X))
    (𝔽 : Filtration (Fin (T + 1)) mΩ) : Set ((Fin (T + 1) → X) → Ω → ℝ) :=
  {z | z ∈ penalties μ A ∧ ∀ α ∈ adaptedPolicies A 𝔽, ∫ ω, z (α ω) ω ∂μ ≤ 0}

/-- `sup_{α ∈ P} 𝔼[f(α)]`, in `EReal`, for a set `P` of policies and a reward-type function
`f(a, ω)`. -/
noncomputable def supValue (μ : Measure Ω) (P : Set (Ω → Fin (T + 1) → X))
    (f : (Fin (T + 1) → X) → Ω → ℝ) : EReal :=
  ⨆ α ∈ P, ((∫ ω, f (α ω) ω ∂μ : ℝ) : EReal)

/-- The value of the primal DP (1), p. 3: `sup_{α ∈ 𝒜_𝔽} 𝔼[r(α)]`. -/
noncomputable def primalValue (μ : Measure Ω) (A : Set (Fin (T + 1) → X))
    (𝔽 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ) : EReal :=
  supValue μ (adaptedPolicies A 𝔽) r

/-- The dual bound of the pair `(𝔾, z)`, the right side of (4), p. 3:
`sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`. -/
noncomputable def dualBound (μ : Measure Ω) (A : Set (Fin (T + 1) → X))
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (r z : (Fin (T + 1) → X) → Ω → ℝ) : EReal :=
  supValue μ (adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω)

/-- The value of the dual problem (6), p. 4: `inf_{z ∈ 𝒵_𝔽} sup_{α_G ∈ 𝒜_𝔾} 𝔼[r(α_G) − z(α_G)]`. -/
noncomputable def dualValue (μ : Measure Ω) (A : Set (Fin (T + 1) → X))
    (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ) : EReal :=
  ⨅ z ∈ dualFeasible μ A 𝔽, dualBound μ A 𝔾 r z

/-- The standing integrability convention on the total reward: `𝔼[r(α)]` exists for every
policy `α ∈ 𝒜`. -/
def RewardIntegrable (μ : Measure Ω) (A : Set (Fin (T + 1) → X))
    (r : (Fin (T + 1) → X) → Ω → ℝ) : Prop :=
  ∀ α ∈ policies (Ω := Ω) A, Integrable (fun ω => r (α ω) ω) μ

end InfoRelax.IdealPenalty


