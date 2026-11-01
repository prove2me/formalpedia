-- Prove2me | Definitions.Def_IDEPoA_FlowOverTime
-- name    : IDEPoA_FlowOverTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:31.53167+00:00
-- url     : https://prove2.me/theorems/2c4cb64e-d79b-4145-b6d4-a435c595cc72
-- title:
--   Single-sink flows over time in the Vickrey queueing model: network, flows, queues, feasibility (1)–(4)
-- statement:
--   This file fixes the flow-over-time model of §2 of Graf and Harks, the deterministic queueing model of Vickrey with a single sink.
--
--   A **network** $\mathcal N$ is a directed multigraph with node set $V$ and edge set $E$, together with a travel time $\tau_e$ and a capacity $\nu_e$ for every edge, a sink $t$, inflow rates $u_v$, and a time $\theta_0$. The standing assumptions are that $\tau_e,\nu_e\ge1$ are integers, $t$ is reachable from every node, $\theta_0\ge0$, and that for $v\ne t$ the rate $u_v$ is nonnegative, integrable and vanishes after $\theta_0$.
--
--   Walks are lists of edges; a simple path is a walk that repeats no node. The physical length of a list is $\sum_e\tau_e$, a physically shortest $v$-$t$ path is a $v$-$t$ walk of minimal physical length, and $\tau(P_{\max})$ is the largest physical length of a simple path to $t$ from any node.
--
--   A **flow over time** is a pair $f=(f^+,f^-)$ of rate functions. It defines
--   $$F_e^\pm(\theta)=\int_0^\theta f_e^\pm(\zeta)\,d\zeta,\quad q_e(\theta)=F_e^+(\theta)-F_e^-(\theta+\tau_e),\quad F_e^\Delta=F_e^+-F_e^-,\quad c_e(\theta)=\tau_e+\frac{q_e(\theta)}{\nu_e},$$
--   the total flow volume $F^\Delta=\sum_eF_e^\Delta$, and the volume at the sink
--   $$Z(\theta)=\sum_{e\in\delta_t^-}F_e^-(\theta)-\sum_{e\in\delta_t^+}F_e^+(\theta).$$
--
--   The flow $f$ is **feasible** if the rates are nonnegative and locally integrable and, for all $\theta\ge0$,
--
--   1. $\sum_{e\in\delta_v^+}f_e^+(\theta)-\sum_{e\in\delta_v^-}f_e^-(\theta)=u_v(\theta)$ for $v\ne t$;
--   2. $\sum_{e\in\delta_t^+}f_e^+(\theta)-\sum_{e\in\delta_t^-}f_e^-(\theta)\le0$;
--   3. $f_e^-(\theta)=0$ for $\theta<\tau_e$;
--   4. $f_e^-(\theta+\tau_e)=\nu_e$ if $q_e(\theta)>0$, and $f_e^-(\theta+\tau_e)=\min\{f_e^+(\theta),\nu_e\}$ otherwise.
--
--   Every other object of the mission is built on these.
--
--   **Formalization Note** The graph is the published `AtomicDynRouting.ResidenceTime.Network`. "Integrable" in the paper is read as locally integrable, since a flow that cycles forever is a flow; constraints hold at every time, as printed. Rates are functions on $\mathbb R$ of which only the values at $\theta\ge0$ matter, and $u_t$ is not used.
-- source:
--   Graf & Harks, The Price of Anarchy for Instantaneous Dynamic Equilibria, arXiv:2007.07794v2, §2, pp.7–9, footnote 3, p.7, Remark 2.9, p.12, Lemma 2.1, p.9

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

open MeasureTheory Set

namespace IDEPoA

/-- A single-sink network `𝒩 = (G, (νₑ), (τₑ), (uᵥ)_{v ≠ t}, t)`
(Graf & Harks, *The Price of Anarchy for Instantaneous Dynamic Equilibria*, arXiv:2007.07794v2,
§2, p.7), together with the end `θ₀` of the network inflow (p.8).

**Formalization Note.** The graph is the published directed multigraph
`AtomicDynRouting.ResidenceTime.Network` (`tail`, `head`), so parallel edges and loops are allowed;
the paper's simple digraph is a special case. Capacities and travel times are natural numbers,
their positivity is part of `Standing`. Rates are functions `ℝ → ℝ` of which only the values at
`θ ≥ 0` matter; `u t` plays no role. -/
structure FlowNetwork (V E : Type) extends AtomicDynRouting.ResidenceTime.Network V E where
  /-- edge travel times `τₑ` -/
  τ : E → ℕ
  /-- edge capacities `νₑ` -/
  ν : E → ℕ
  /-- the sink `t` -/
  t : V
  /-- the network inflow rates `uᵥ`; only `v ≠ t` is used -/
  u : V → ℝ → ℝ
  /-- a time after which all network inflow rates vanish (p.8) -/
  θ₀ : ℝ

variable {V E : Type}

/-- `IsWalk N v w p`: the edge list `p` is a directed `v`-`w` walk of `N`. It may repeat nodes. -/
abbrev IsWalk (N : FlowNetwork V E) (v w : V) (p : List E) : Prop :=
  N.toNetwork.IsPathFrom v w p

/-- The nodes visited by the edge list `p` when it is started at `v`, in order. -/
def walkNodes (N : FlowNetwork V E) : V → List E → List V
  | v, [] => [v]
  | v, e :: p => v :: walkNodes N (N.head e) p

/-- A simple `v`-`w` path: a walk that repeats no node. -/
def IsPath (N : FlowNetwork V E) (v w : V) (p : List E) : Prop :=
  IsWalk N v w p ∧ (walkNodes N v p).Nodup

/-- The physical length `∑_{e ∈ p} τₑ` of an edge list. -/
def physLength (N : FlowNetwork V E) (p : List E) : ℕ := (p.map N.τ).sum

/-- The physical distance from `v` to the sink: the minimal physical length of a `v`-`t` walk
(`Standing` makes the set nonempty). A shortest walk is a simple path since `τₑ ≥ 1`. -/
noncomputable def physDist (N : FlowNetwork V E) (v : V) : ℕ :=
  sInf {n : ℕ | ∃ p, IsWalk N v N.t p ∧ physLength N p = n}

/-- `p` is a physically shortest `v`-`t` path (p.11: "paths that are minimal with respect to the
transit times τ"). -/
def IsPhysShortest (N : FlowNetwork V E) (v : V) (p : List E) : Prop :=
  IsWalk N v N.t p ∧ physLength N p = physDist N v

/-- `τ(Pmax)` (p.13: "the physical length of a longest v-t path"), over all nodes `v`.

**Formalization Note.** The supremum is over **simple** paths: over walks it would be infinite on a
network with a cycle. There are finitely many simple paths in a finite network, so the set is bounded
above and nonempty, and the `sSup` in `ℕ` is a maximum (`IDEPoA_structure.lean` verifies this). -/
noncomputable def tauPmax (N : FlowNetwork V E) : ℕ :=
  sSup {n : ℕ | ∃ v p, IsPath N v N.t p ∧ physLength N p = n}

/-- The standing assumptions of the paper on a network (§2, pp.7–8, footnote 3 and Remark 2.9):
travel times and capacities are positive integers, the sink is reachable from every node, and for
`v ≠ t` the inflow rate `uᵥ` is nonnegative, integrable and supported in `[0, θ₀]`, `θ₀ ≥ 0`. -/
structure Standing (N : FlowNetwork V E) : Prop where
  τ_pos : ∀ e, 0 < N.τ e
  ν_pos : ∀ e, 0 < N.ν e
  θ₀_nonneg : 0 ≤ N.θ₀
  reachable : ∀ v, ∃ p, IsWalk N v N.t p
  u_nonneg : ∀ v, v ≠ N.t → ∀ θ : ℝ, 0 ≤ θ → 0 ≤ N.u v θ
  u_integrable : ∀ v, v ≠ N.t → IntegrableOn (N.u v) (Ici 0)
  u_support : ∀ v, v ≠ N.t → ∀ θ : ℝ, N.θ₀ < θ → N.u v θ = 0

/-- A flow over time `f = (f⁺, f⁻)` (p.7): the edge in- and outflow rates. Only times `θ ≥ 0`
matter. -/
structure Flow (E : Type) where
  /-- the edge inflow rates `fₑ⁺` -/
  fplus : E → ℝ → ℝ
  /-- the edge outflow rates `fₑ⁻` -/
  fminus : E → ℝ → ℝ

/-- The cumulative edge inflow `Fₑ⁺(θ) = ∫₀^θ fₑ⁺` (p.8). -/
noncomputable def Fplus (f : Flow E) (e : E) (θ : ℝ) : ℝ := ∫ ζ in (0 : ℝ)..θ, f.fplus e ζ

/-- The cumulative edge outflow `Fₑ⁻(θ) = ∫₀^θ fₑ⁻` (p.8). -/
noncomputable def Fminus (f : Flow E) (e : E) (θ : ℝ) : ℝ := ∫ ζ in (0 : ℝ)..θ, f.fminus e ζ

/-- The queue length `qₑ(θ) = Fₑ⁺(θ) − Fₑ⁻(θ + τₑ)` (p.8). -/
noncomputable def queue (N : FlowNetwork V E) (f : Flow E) (e : E) (θ : ℝ) : ℝ :=
  Fplus f e θ - Fminus f e (θ + N.τ e)

/-- The edge load `Fₑ^Δ(θ) = Fₑ⁺(θ) − Fₑ⁻(θ)` (p.8). -/
noncomputable def load (f : Flow E) (e : E) (θ : ℝ) : ℝ := Fplus f e θ - Fminus f e θ

/-- The instantaneous travel time `cₑ(θ) = τₑ + qₑ(θ)/νₑ` (p.10). `νₑ ≥ 1` by `Standing`. -/
noncomputable def cost (N : FlowNetwork V E) (f : Flow E) (e : E) (θ : ℝ) : ℝ :=
  N.τ e + queue N f e θ / N.ν e

/-- The cumulative network inflow `Uᵥ(θ) = ∫₀^θ uᵥ` (p.9), for `v ≠ t`. -/
noncomputable def cumU (N : FlowNetwork V E) (v : V) (θ : ℝ) : ℝ := ∫ ζ in (0 : ℝ)..θ, N.u v ζ

section Sums

variable [Fintype V] [Fintype E] [DecidableEq V]

/-- `δᵥ⁺`: the edges leaving `v` (p.8). A loop at `v` is in both `δᵥ⁺` and `δᵥ⁻`. -/
def outEdges (N : FlowNetwork V E) (v : V) : Finset E :=
  Finset.univ.filter fun e => N.tail e = v

/-- `δᵥ⁻`: the edges entering `v` (p.8). -/
def inEdges (N : FlowNetwork V E) (v : V) : Finset E :=
  Finset.univ.filter fun e => N.head e = v

/-- `E(W)`: all edges with both end nodes in `W` (Lemma 2.1, p.9), loops included. -/
def edgesIn (N : FlowNetwork V E) (W : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∈ W ∧ N.head e ∈ W

/-- `δ_W⁺`: the edges from `W` to `V ∖ W` (Lemma 2.1, p.9). -/
def outOf (N : FlowNetwork V E) (W : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∈ W ∧ N.head e ∉ W

/-- `δ_W⁻`: the edges from `V ∖ W` to `W` (Lemma 2.1, p.9). -/
def into (N : FlowNetwork V E) (W : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∉ W ∧ N.head e ∈ W

/-- The total flow volume in the network `F^Δ(θ) = ∑ₑ Fₑ^Δ(θ)` (p.8). -/
noncomputable def totalLoad (f : Flow E) (θ : ℝ) : ℝ := ∑ e, load f e θ

/-- `Z(θ) = ∑_{e ∈ δₜ⁻} Fₑ⁻(θ) − ∑_{e ∈ δₜ⁺} Fₑ⁺(θ)`, display (5), p.8: the flow volume that has
reached the sink by time `θ`. Net of the outflow from `t`. -/
noncomputable def Z (N : FlowNetwork V E) (f : Flow E) (θ : ℝ) : ℝ :=
  ∑ e ∈ inEdges N N.t, Fminus f e θ - ∑ e ∈ outEdges N N.t, Fplus f e θ

/-- The density `∑_{e ∈ δₜ⁻} fₑ⁻(θ) − ∑_{e ∈ δₜ⁺} fₑ⁺(θ)` of `Z`, which is the `Z′` of Lemma 2.5
(p.10). It stands for the derivative, which exists only almost everywhere. -/
noncomputable def Zrate (N : FlowNetwork V E) (f : Flow E) (θ : ℝ) : ℝ :=
  ∑ e ∈ inEdges N N.t, f.fminus e θ - ∑ e ∈ outEdges N N.t, f.fplus e θ

/-- `f` is a feasible flow for `N` (p.8), constraints (1)–(4), and `f⁺`, `f⁻` are nonnegative and
integrable (p.7).

**Formalization Note.** "Integrable" (p.7) is read as locally integrable on `ℝ≥0`: `F⁺` and `F⁻`
only need `∫₀^θ`, and global integrability would exclude forever-cycling flows up front, which the
paper treats as flows (the termination of an IDE is a theorem, not an assumption). The constraints
hold for all `θ ≥ 0`, as printed, not almost everywhere; (3) reads `0 ≤ θ < τₑ`. -/
structure IsFeasible (N : FlowNetwork V E) (f : Flow E) : Prop where
  fplus_nonneg : ∀ (e : E) (θ : ℝ), 0 ≤ θ → 0 ≤ f.fplus e θ
  fminus_nonneg : ∀ (e : E) (θ : ℝ), 0 ≤ θ → 0 ≤ f.fminus e θ
  fplus_integrable : ∀ (e : E) (T : ℝ), IntegrableOn (f.fplus e) (Icc 0 T)
  fminus_integrable : ∀ (e : E) (T : ℝ), IntegrableOn (f.fminus e) (Icc 0 T)
  /-- flow conservation, (1), p.8 -/
  conservation : ∀ v, v ≠ N.t → ∀ θ : ℝ, 0 ≤ θ →
    ∑ e ∈ outEdges N v, f.fplus e θ - ∑ e ∈ inEdges N v, f.fminus e θ = N.u v θ
  /-- the sink inequality, (2), p.8 -/
  sink : ∀ θ : ℝ, 0 ≤ θ →
    ∑ e ∈ outEdges N N.t, f.fplus e θ - ∑ e ∈ inEdges N N.t, f.fminus e θ ≤ 0
  /-- no outflow before `τₑ`, (3), p.8 -/
  no_early_outflow : ∀ (e : E) (θ : ℝ), 0 ≤ θ → θ < N.τ e → f.fminus e θ = 0
  /-- queues operate at capacity, (4), p.8 -/
  capacity : ∀ (e : E) (θ : ℝ), 0 ≤ θ →
    f.fminus e (θ + N.τ e) =
      if 0 < queue N f e θ then (N.ν e : ℝ) else min (f.fplus e θ) (N.ν e)

end Sums

end IDEPoA


