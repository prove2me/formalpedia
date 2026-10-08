-- Prove2me | Definitions.Def_InfoRelax_RelaxOrder_Framework
-- name    : InfoRelax_RelaxOrder_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:04.030118+00:00
-- url     : https://prove2.me/theorems/2482ecac-312e-4223-bef1-f4922afab237
-- title:
--   Policies, information relaxations, penalties and dual bounds (§2.1–§2.2)
-- statement:
--   This file sets up the general framework of Brown, Smith and Sun for a finite-horizon stochastic dynamic program and its information-relaxation dual.
--
--   Uncertainty is a probability space $(\Omega,\mathcal F,\mathbb P)$. Time is $t=0,\dots,T$, and an **action sequence** is $a=(a_0,\dots,a_T)$ with actions in a measurable space $X$; a set $A$ of action sequences is the **feasible set**. The total reward is a function $r(a,\omega)$. A **filtration** $\mathbb G=(\mathcal G_0,\dots,\mathcal G_T)$ is an increasing family of sub-$\sigma$-algebras of $\mathcal F$.
--
--   1. **Policies.** A policy is a map $\alpha:\Omega\to A$. It is **adapted to $\mathbb G$** if each action $\omega\mapsto\alpha(\omega)_t$ is $\mathcal G_t$-measurable; $\mathcal A_{\mathbb G}$ is the set of such policies. The **perfect-information filtration** $\mathbb I$ has $\mathcal I_t=\mathcal F$ for all $t$, and $\mathcal A=\mathcal A_{\mathbb I}$ is the set of all (measurable) policies.
--   2. **Relaxations.** $\mathbb G$ is a **relaxation** of $\mathbb F$ if $\mathcal F_t\subseteq\mathcal G_t\subseteq\mathcal F$ for every $t$, written $\mathbb F\subseteq\mathbb G$.
--   3. **Penalties.** The penalty set $\mathcal Z$ consists of the functions $z(a,\omega)$ for which $\mathbb E[z(\alpha)]=\mathbb E[z(\alpha(\omega),\omega)]$ exists for every $\alpha\in\mathcal A$. The **dual feasible penalties** are
--   $$\mathcal Z_{\mathbb F}=\{z\in\mathcal Z:\ \mathbb E[z(\alpha_F)]\le 0\ \text{for all }\alpha_F\in\mathcal A_{\mathbb F}\}.\qquad(3)$$
--   4. **Values.** For a set $P$ of policies and a function $f(a,\omega)$, $\sup_{\alpha\in P}\mathbb E[f(\alpha)]$ and $\inf_{\alpha\in P}\mathbb E[f(\alpha)]$ are taken in the extended reals. The **dual bound** of a pair $(\mathbb G,z)$, the right side of (4), is
--   $$\sup_{\alpha_G\in\mathcal A_{\mathbb G}}\mathbb E[r(\alpha_G)-z(\alpha_G)].$$
--   5. **Integrable rewards.** The reward is integrable if $\mathbb E[r(\alpha)]$ exists for every $\alpha\in\mathcal A$.
--
--   Every comparison of information relaxations and penalties in Proposition 2.3 is a comparison of such dual bounds.
--
--   **Formalization Note** One action type $X$ serves every period (the disjoint union of the page's $A_t$). Adaptedness of each action is equivalent to the page's "the first $t+1$ actions are $\mathcal F_t$-measurable" because filtrations increase. Integrability is the field's standing convention, which the page leaves implicit. Values are in `EReal`, so that an empty set of policies gives $\mp\infty$ and an unbounded one $\pm\infty$ rather than a default $0$; differences such as $r-z$ are integrated as real functions and never subtracted in `EReal`.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, pp. 2–3, §2.1 (policies, nonanticipative policies) and §2.2 (relaxations, the penalty set, eq. (3), right side of (4))

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-!
# The general framework of Brown, Smith & Sun (2010), §2.1–§2.2

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, pp. 2–3:
§2.1 "General Framework" (policies, nonanticipative policies) and §2.2 "The Dual Approach"
(relaxations, the penalty set `𝒵`, dual feasible penalties (3), the dual bound on the right
of (4)).

Periods are `t : Fin (T + 1)` (the page's `t = 0, …, T`); an action sequence is
`a : Fin (T + 1) → X`; `A` is the set of feasible action sequences; `r a ω` is the total reward.
A filtration of the ambient σ-algebra `mΩ` (the page's `𝓕`) is a Mathlib `Filtration`, which
already encodes `𝓕_t ⊆ 𝓕_{t+1} ⊆ 𝓕`.

**Formalization Note.**
* One action type `X` for every period (take `X` to be the disjoint union of the page's `A_t`).
* A policy is adapted to `𝔾` when each action `ω ↦ α ω t` is `𝔾 t`-measurable. Because `𝔾` is
  increasing this is equivalent to the page's "the selection of the first `t + 1` actions is
  `𝒢_t`-measurable".
* `𝒜` (`policies`) is the set of policies adapted to the perfect-information filtration
  (`𝒥_t = 𝓕`), i.e. the measurable policies; the page's `𝒜_𝕀 = 𝒜` (p. 3).
* Integrability is the field's standing convention, unstated on the page: a penalty in `𝒵` is
  integrable along every policy of `𝒜`, and `RewardIntegrable` says the same of the reward.
* Values are in `EReal` and are suprema/infima over the adapted subsets, so that `±∞` are values
  and an empty set of policies gives `⊥`/`⊤` rather than a junk `0`. Differences such as `r − z`
  are integrated as real functions and then coerced; no `EReal` subtraction occurs here.
* The objects above (`adaptedPolicies`, `policies`, `IsRelaxation`, `penalties`, `dualFeasible`,
  `supValue`, `dualBound`, `RewardIntegrable`) are those of the shared module
  `InfoRelax.IdealPenalty.Framework`; this file adds only `infValue`, the left side of (13).
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X] {T : ℕ}

/-- `inf_{α ∈ P} 𝔼[f(α)]`, in `EReal`, for a set `P` of policies and a function `f(a, ω)`. -/
noncomputable def infValue (μ : Measure Ω) (P : Set (Ω → Fin (T + 1) → X))
    (f : (Fin (T + 1) → X) → Ω → ℝ) : EReal :=
  ⨅ α ∈ P, ((∫ ω, f (α ω) ω ∂μ : ℝ) : EReal)

end InfoRelax.RelaxOrder


