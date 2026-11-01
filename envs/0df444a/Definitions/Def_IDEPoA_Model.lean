-- Prove2me | Definitions.Def_IDEPoA_Model
-- name    : IDEPoA_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:25.602925+00:00
-- url     : https://prove2.me/theorems/4f061aec-558f-42f7-a9bb-be29c6d5bb97
-- title:
--   Instantaneous dynamic equilibria: labels, IDE (7), makespan, total travel times, PoA, sink-like subgraphs (corrected: $t\in T$)
-- statement:
--   This file defines the equilibrium concept and the objectives of Graf and Harks.
--
--   The **labels** $\ell_v(\theta)$ are the shortest $v$-$t$ distances with respect to the instantaneous travel times $c_e(\theta)$, and an edge $e=vw$ is **active** at $\theta$ if $\ell_v(\theta)=\ell_w(\theta)+c_e(\theta)$. A feasible flow $f$ is an **instantaneous dynamic equilibrium** (IDE) if for all $\theta\ge0$ and all $e$
--   $$f_e^+(\theta)>0\ \Longrightarrow\ e\text{ is active at }\theta.$$
--
--   The **makespan** is $\Theta(f)=\inf\{\theta\ge\theta_0\mid F^\Delta(\theta)=0\}$, which is $\infty$ for a flow that does not terminate, and the **total travel times** are $\Xi(f)=\sum_e\int_0^\infty c_e(\theta)f_e^+(\theta)\,d\theta$. For an instance $\mathcal N$,
--   $$\Theta_{\mathrm{IDE}}=\sup_{f\text{ IDE}}\Theta(f),\quad\Theta_{\mathrm{OPT}}=\inf_{f\text{ feasible}}\Theta(f),\quad\Xi_{\mathrm{IDE}}=\sup_{f\text{ IDE}}\Xi(f),\quad\Xi_{\mathrm{OPT}}=\inf_{f}\Xi(f).$$
--   The prices of anarchy $\mathrm{M\text{-}PoA}(U,\tau)$ and $\mathrm{T\text{-}PoA}(U,\tau)$ are the suprema of $\Theta_{\mathrm{IDE}}/\Theta_{\mathrm{OPT}}$ and $\Xi_{\mathrm{IDE}}/\Xi_{\mathrm{OPT}}$ over the instances with total flow volume $U=\sum_{v\ne t}\int_0^{\theta_0}u_v$ and total edge length $\tau=\sum_e\tau_e$.
--
--   The induced subgraph on a node set $T$ containing $t$ is **sink-like** on $[\theta_1,\theta_2]$ if all physically shortest $v$-$t$ paths from nodes $v\in T$ stay in $T$ and
--   $$\mathrm{vol}_T(\theta_1,\theta_2)=\sum_{e\in E(T)}F_e^\Delta(\theta_1)+\sum_{e\in\delta_T^-}\int_{\theta_1}^{\theta_2}f_e^-+\sum_{v\in T\setminus\{t\}}\int_{\theta_1}^{\theta_2}u_v<\frac12.$$
--
--   **Formalization Note** The labels are the infimum of the walk costs, a function of the flow; for a feasible flow they satisfy the recursion (6) of the paper. All objectives are in $[0,\infty]$, and $\Xi$ is a lower integral, so that a divergent integral has the value $\infty$. Definition 2.4 states $\Xi$ for terminating flows; here its formula is used for every flow, so $\Xi_{\mathrm{OPT}}$ ranges over all feasible flows, as printed on p.11 (an infimum at most the one over terminating flows), and $\Xi_{\mathrm{IDE}}$ ranges over all IDE flows: their termination is Theorem 3.9, not an assumption. Definition 3.5 is printed without $t\in T$; the condition excludes exactly the empty subgraph, for which Lemma 3.8 is false. The interval conditions $0\le\theta_1\le\theta_2$ are part of the sink-like predicate.
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, (6) and Definition 2.7, p.11; Definitions 2.3, 2.4, p.10; p.11; Definition 2.8, p.12; Definition 3.5, p.17

import Mathlib
import Definitions.Def_IDEPoA_FlowOverTime

open MeasureTheory Set
open scoped ENNReal

namespace IDEPoA

variable {V E : Type}

/-- The node label `ℓᵥ(θ)` of display (6), p.11: the length of a shortest `v`-`t` walk with respect
to the instantaneous travel times `cₑ(θ)`.

**Formalization Note.** The paper defines `ℓ` by the recursion (6). Here it is the infimum of the
walk costs, a function of the flow rather than a free variable. For a feasible flow all `cₑ` are
positive, the set is nonempty and bounded below by `0`, and `ℓ` satisfies (6)
(`IDEPoA_structure.lean` verifies this). -/
noncomputable def label (N : FlowNetwork V E) (f : Flow E) (v : V) (θ : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ p, IsWalk N v N.t p ∧ c = (p.map fun e => cost N f e θ).sum}

/-- The edge `e = vw` is active at time `θ`, `e ∈ E_θ`: `ℓᵥ(θ) = ℓ_w(θ) + cₑ(θ)` (p.11). -/
def IsActive (N : FlowNetwork V E) (f : Flow E) (e : E) (θ : ℝ) : Prop :=
  label N f (N.tail e) θ = label N f (N.head e) θ + cost N f e θ

/-- `p` is an active `v`-`t` walk at time `θ` (p.11): a `v`-`t` walk all of whose edges are
active. Such a walk is a path, as the labels strictly decrease along it. -/
def IsActiveWalk (N : FlowNetwork V E) (f : Flow E) (θ : ℝ) (v : V) (p : List E) : Prop :=
  IsWalk N v N.t p ∧ ∀ e ∈ p, IsActive N f e θ

section Sums

variable [Fintype V] [Fintype E] [DecidableEq V]

/-- `f` is an instantaneous dynamic equilibrium (IDE), Definition 2.7, p.11: a feasible flow with
`fₑ⁺(θ) > 0 ⇒ e ∈ E_θ` for all `θ ≥ 0` and all `e`, display (7). -/
def IsIDE (N : FlowNetwork V E) (f : Flow E) : Prop :=
  IsFeasible N f ∧ ∀ θ : ℝ, 0 ≤ θ → ∀ e, 0 < f.fplus e θ → IsActive N f e θ

/-- The makespan `Θ(f) = inf {θ ≥ θ₀ | F^Δ(θ) = 0}`, Definition 2.3, p.10. It is `⊤` for a
non-terminating flow, as the infimum over an empty set. -/
noncomputable def makespan (N : FlowNetwork V E) (f : Flow E) : ℝ≥0∞ :=
  ⨅ θ ∈ {θ : ℝ | N.θ₀ ≤ θ ∧ totalLoad f θ = 0}, ENNReal.ofReal θ

/-- `f` terminates (Definition 2.3, p.10). -/
def Terminates (N : FlowNetwork V E) (f : Flow E) : Prop := makespan N f < ⊤

/-- The total travel times `Ξ(f) = ∑ₑ ∫₀^∞ cₑ(θ) fₑ⁺(θ) dθ`, Definition 2.4, p.10.

**Formalization Note.** A lower Lebesgue integral in `ℝ≥0∞`, not a Bochner integral, so that the
value of a non-integrable integrand is `⊤` and not `0`. The paper defines `Ξ` for terminating flows;
the formula makes sense for every feasible flow, whose integrand is nonnegative. -/
noncomputable def totalTravel (N : FlowNetwork V E) (f : Flow E) : ℝ≥0∞ :=
  ∑ e, ∫⁻ θ in Ici (0 : ℝ), ENNReal.ofReal (cost N f e θ * f.fplus e θ)

/-- The worst case makespan of an IDE flow, `Θ_IDE(𝒩)`, p.11. -/
noncomputable def thetaIDE (N : FlowNetwork V E) : ℝ≥0∞ :=
  ⨆ f : Flow E, ⨆ _ : IsIDE N f, makespan N f

/-- The optimal makespan `Θ_OPT(𝒩)`, p.11, over all feasible flows; a non-terminating flow has
makespan `⊤`. -/
noncomputable def thetaOPT (N : FlowNetwork V E) : ℝ≥0∞ :=
  ⨅ f : Flow E, ⨅ _ : IsFeasible N f, makespan N f

/-- The worst case total travel times of an IDE flow, `Ξ_IDE(𝒩)`, p.11. Over **all** IDE flows:
that every IDE flow terminates is Theorem 3.9, not an assumption. -/
noncomputable def xiIDE (N : FlowNetwork V E) : ℝ≥0∞ :=
  ⨆ f : Flow E, ⨆ _ : IsIDE N f, totalTravel N f

/-- The optimal total travel times `Ξ_OPT(𝒩) = inf {Ξ(f) | f a feasible flow in 𝒩}`, p.11.

**Formalization Note.** Over **all** feasible flows, as printed, with `Ξ` given by the formula of
Definition 2.4 (a lower integral, so defined on every flow). Definition 2.4 states `Ξ` for
terminating flows; the infimum here is at most the infimum over terminating flows, so a bound on
`Ξ_IDE / Ξ_OPT` with this `Ξ_OPT` implies the bound with the restricted one. -/
noncomputable def xiOPT (N : FlowNetwork V E) : ℝ≥0∞ :=
  ⨅ f : Flow E, ⨅ _ : IsFeasible N f, totalTravel N f

/-- The total flow volume `U = ∑_{v ≠ t} Uᵥ(θ₀)` of a network (Definition 2.8, p.12; §3, p.12). -/
noncomputable def totalVolume (N : FlowNetwork V E) : ℝ :=
  ∑ v ∈ Finset.univ.erase N.t, cumU N v N.θ₀

/-- The total edge length `τ(G) = ∑ₑ τₑ` (§3, p.12). -/
def totalLength (N : FlowNetwork V E) : ℕ := ∑ e, N.τ e

/-- The weight `τₑ + 1/(2νₑ)` of an edge, the summand of Lemma 3.8 and Theorem 3.9. -/
noncomputable def edgeWeight (N : FlowNetwork V E) (e : E) : ℝ :=
  N.τ e + 1 / (2 * N.ν e)

/-- The sum `∑ₑ (τₑ + 1/(2νₑ))` of Claim 5 and Theorem 3.9. -/
noncomputable def weightSum (N : FlowNetwork V E) : ℝ := ∑ e, edgeWeight N e

/-- `vol_T(θ₁, θ₂)`, Definition 3.5, p.17: the flow volume present in `T` at `θ₁` plus the
cumulative inflow into `T` during `[θ₁, θ₂]`. -/
noncomputable def vol (N : FlowNetwork V E) (f : Flow E) (T : Finset V) (θ₁ θ₂ : ℝ) : ℝ :=
  ∑ e ∈ edgesIn N T, load f e θ₁ + ∑ e ∈ into N T, ∫ θ in θ₁..θ₂, f.fminus e θ
    + ∑ v ∈ T.erase N.t, ∫ θ in θ₁..θ₂, N.u v θ

/-- The subgraph induced by the node set `T` is sink-like on the interval `[θ₁, θ₂]` of times,
Definition 3.5, p.17 (corrected: `t ∈ T`).

The definition asks that every physically shortest `v`-`t` path from a node `v ∈ T` stays in `T`
and that `vol_T(θ₁, θ₂) < 1/2`. The printed definition omits `t ∈ T`, which excludes exactly the
empty subgraph: for it Lemma 3.8 is false (`IDEPoA_oneEdge.lean`). -/
structure IsSinkLike (N : FlowNetwork V E) (f : Flow E) (T : Finset V) (θ₁ θ₂ : ℝ) : Prop where
  sink_mem : N.t ∈ T
  nonneg : 0 ≤ θ₁
  le : θ₁ ≤ θ₂
  shortest_inside : ∀ v ∈ T, ∀ p, IsPhysShortest N v p → ∀ w ∈ walkNodes N v p, w ∈ T
  vol_lt : vol N f T θ₁ θ₂ < 1 / 2

end Sums

/-- An instance of the model (§2): a finite network satisfying the standing assumptions. -/
structure Instance where
  V : Type
  E : Type
  [fintypeV : Fintype V]
  [fintypeE : Fintype E]
  [decEqV : DecidableEq V]
  net : FlowNetwork V E
  standing : Standing net

attribute [instance] Instance.fintypeV Instance.fintypeE Instance.decEqV

/-- The makespan price of anarchy `M-PoA(U, τ)`, Definition 2.8, p.12: the supremum of
`Θ_IDE(𝒩)/Θ_OPT(𝒩)` over the instances with total flow volume `U` and total edge length `τ`.

**Formalization Note.** The ratio is in `ℝ≥0∞`, where `a / ⊤ = 0`. Every instance has a terminating
feasible flow by reachability, so `Θ_OPT < ⊤`, and `Θ_OPT ≥ 1` for `U ≥ 1` (milestone
`opt_lower_bounds`), so that neither `a / ⊤` nor `a / 0` arises. `θ₀` is part of the instance and
is not assumed tight. -/
noncomputable def MPoA (U τ : ℕ) : ℝ≥0∞ :=
  ⨆ I : Instance, ⨆ _ : totalVolume I.net = U ∧ totalLength I.net = τ,
    thetaIDE I.net / thetaOPT I.net

/-- The total travel times price of anarchy `T-PoA(U, τ)`, Definition 2.8, p.12: the supremum of
`Ξ_IDE(𝒩)/Ξ_OPT(𝒩)` over the instances with total flow volume `U` and total edge length `τ`. The
ratio is in `ℝ≥0∞`, as for `MPoA`. -/
noncomputable def TPoA (U τ : ℕ) : ℝ≥0∞ :=
  ⨆ I : Instance, ⨆ _ : totalVolume I.net = U ∧ totalLength I.net = τ,
    xiIDE I.net / xiOPT I.net

end IDEPoA


