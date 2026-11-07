-- Prove2me | Definitions.Def_IncrementalER_hitBefore
-- name    : IncrementalER_hitBefore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:49.3006+00:00
-- url     : https://prove2.me/theorems/d123dac8-65c1-47ec-91ca-4de4b82964d7
-- title:
--   Random walks: $p_u(\tau_v<\tau_B)$, $\Gamma_T$, $\alpha$-hitting sets, visit counts, escape probabilities, $R_{\mathrm{eff}}(v,S)$
-- statement:
--   The standard random walk on $G$ moves from $u$ to $v$ with probability $P(u,v)=c_{uv}/d_u$; $\tau_S=\inf\{t\ge0:u_t\in S\}$ and $\tau_{v+}=\inf\{t\ge1:u_t=v\}$. All probabilities are sums of path weights $\prod_iP(u_i,u_{i+1})$.
--
--   1. $p_u(\tau_v<\tau_B)$ is the probability that the walk from $u$ reaches $v$ before the set $B$ (p.12).
--   2. $\Gamma_T(v)=\sum_{u\notin T}\deg(u)\,p_u(\tau_v<\tau_T)$ (equation (3)).
--   3. $T$ is an **$\alpha$-hitting set with congestion bound $\beta$** if for every $v\notin T$: $\mathbb E_v[|\{u_0,\dots,u_{\tau_T-1}\}|]\le\alpha$, $\Gamma_T(v)\le\beta$, and $\deg(v)\le\alpha$ (Definition 3.9 with its $\tilde O(\alpha^2)$ written as $\beta$).
--   4. $\mathbb E_v[N_u(\tau_S)]$, the expected number of visits to $u$ before the walk from $v$ reaches $S$, and $p_v(\tau_S<\tau_{v+})$ (p.29).
--   5. $R_{\mathrm{eff}}(v,S)$, the minimum electrical energy $\sum_e\theta_e^2/c_e$ of a unit flow from $v$ to the set $S$ (footnote 7).
--
--   These quantities connect leverage degrees and grounded inverses to walks, which is how the paper estimates leverage degrees by sampling.
--
--   **Formalization Note** The expected number of distinct vertices is written $\sum_{w\notin T}p_v(\tau_w<\tau_T)$ by linearity of expectation; this is exact also for $T=\emptyset$. The walk and the path weights are the published `MarkovMixing` network layer. $R_{\mathrm{eff}}(v,S)$ is a real infimum over unit flows (net outflow $1$ at $v$, $0$ at the other vertices outside $S$), attained when $G$ is connected and $S\neq\emptyset$.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), random walks, p.12; (3) and Definition 3.9, p.13; §5.1 and footnote 7, p.29

import Mathlib
import Definitions.Def_mm_network
import Definitions.Def_IncrementalER_lap

namespace IncrementalER

/-!
# The standard random walk: hitting probabilities, `Γ_T`, hitting sets, visit counts,
# escape probabilities and the effective resistance to a set

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), §3 "Random Walks &
Hitting Sets" (p.12), (3) and Definition 3.9 (p.13), §5.1 (p.29) and footnote 7 (p.29).

**Formalization Note.**
* The walk is the published `MarkovMixing.networkWalk c`, `P(u, v) = c_uv / d_u` (p.12), and every
  probability is a sum of path weights `∏ P(u_i, u_{i+1})` over finite trajectories
  (`MarkovMixing.pathWeight`); no probability is defined by a linear-algebra formula.
* `τ_S = inf{t ≥ 0 : u_t ∈ S}` (p.12). `p_u(τ_v < τ_B)` (for `v ∉ B`) is the probability that the
  walk from `u` first enters `B ∪ {v}` at `v`: the published `MarkovMixing.firstHitAtProb`. It is
  `1` for `u = v`, `0` for `u ∈ B`, and with `B = ∅` it is the probability of ever reaching `v`.
* Item 1 of Definition 3.9, `E_v[|{u_0, …, u_{τ_T − 1}}|]`, is written by linearity of expectation
  as `∑_{w ∉ T} p_v(τ_w < τ_T)`: a vertex `w ∉ T` is among `u_0, …, u_{τ_T − 1}` iff the walk
  reaches `w` before `T`. This is exact also when `T = ∅` (`τ_∅ = ∞`).
* `Õ(α²)` in item 2 of Definition 3.9 has no meaning without a constant, so the bound is a
  parameter `β`: `IsHittingSet c T α β`.
* `N_u(τ_S) = |{t ≤ τ_S : u_t = u}|` (p.29); for `u ∉ S` this counts the visits at times
  `t < τ_S`. `τ_{v+} = inf{t ≥ 1 : u_t = v}` (p.29).
* `Reff(v, S)` is the minimum energy `∑_e θ_e² / c_e` (each edge once, the published
  `MarkovMixing.flowEnergy`) of a unit flow from `v` to `S` (footnote 7): an antisymmetric flow on
  edges of positive conductance with net outflow `1` at `v`, `0` at every other vertex outside `S`,
  and arbitrary net inflow at the vertices of `S`. The infimum is a real `sInf` of a set of
  nonnegative reals that is nonempty when `G` is connected, `v ∉ S` and `S ≠ ∅`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `p_u(τ_v < τ_B)`: the walk started at `u` reaches `v` before the set `B` (p.12). -/
noncomputable def hitBefore (c : V → V → ℝ) (u v : V) (B : Finset V) : ℝ :=
  MarkovMixing.firstHitAtProb (MarkovMixing.networkWalk c) u (insert v B) v

/-- `Γ_T(v) = ∑_{u ∉ T} deg(u) p_u(τ_v < τ_T)` ((3), p.13). -/
noncomputable def gammaT (c : V → V → ℝ) (T : Finset V) (v : V) : ℝ :=
  ∑ u ∈ Finset.univ.filter (· ∉ T), (deg c u : ℝ) * hitBefore c u v T

/-- `E_v[|{u_0, …, u_{τ_T − 1}}|] = ∑_{w ∉ T} p_v(τ_w < τ_T)`, the expected number of distinct
vertices visited from `v` before reaching `T` (Definition 3.9, item 1). -/
noncomputable def expDistinct (c : V → V → ℝ) (v : V) (T : Finset V) : ℝ :=
  ∑ w ∈ Finset.univ.filter (· ∉ T), hitBefore c v w T

/-- `T` is an `α`-hitting set of `G` with congestion bound `β` (Definition 3.9, p.13): for every
`v ∉ T`, (1) `E_v[|{u_0, …, u_{τ_T − 1}}|] ≤ α`, (2) `Γ_T(v) ≤ β`, (3) `deg(v) ≤ α`. -/
def IsHittingSet (c : V → V → ℝ) (T : Finset V) (α β : ℝ) : Prop :=
  ∀ v, v ∉ T → expDistinct c v T ≤ α ∧ gammaT c T v ≤ β ∧ (deg c v : ℝ) ≤ α

/-- `E_v[N_u(τ_S)] = ∑_{t ≥ 0} P_v(u_t = u, τ_S > t)`, the expected number of visits to `u` before
the walk from `v` reaches `S` (p.29). -/
noncomputable def expVisits (c : V → V → ℝ) (v : V) (S : Finset V) (u : V) : ℝ :=
  ∑' t : ℕ, MarkovMixing.avoidSetAtProb (MarkovMixing.networkWalk c) v S u t

/-- `p_v(τ_S < τ_{v+})`: the walk from `v` reaches `S` at some time `t + 1 ≥ 1` without visiting
`v` at any time in `1, …, t + 1` (p.29). -/
noncomputable def escapeProb (c : V → V → ℝ) (v : V) (S : Finset V) : ℝ :=
  ∑' t : ℕ, ∑ ω : Fin (t + 2) → V,
    if ω 0 = v ∧ (∀ i : Fin (t + 2), i ≠ 0 → ω i ≠ v) ∧
        (∀ i : Fin (t + 2), i ≠ Fin.last (t + 1) → ω i ∉ S) ∧ ω (Fin.last (t + 1)) ∈ S then
      MarkovMixing.pathWeight (MarkovMixing.networkWalk c) ω
    else 0

/-- `θ` is a unit flow from `v` into the set `S`: antisymmetric, zero on edges of zero
conductance, net outflow `1` at `v` and `0` at every other vertex outside `S`. -/
def IsUnitFlowToSet (c : V → V → ℝ) (θ : V → V → ℝ) (v : V) (S : Finset V) : Prop :=
  (∀ x y, θ x y = -θ y x) ∧ (∀ x y, c x y = 0 → θ x y = 0) ∧
    ∀ x, x ∉ S → ∑ y, θ x y = if x = v then 1 else 0

/-- `Reff(v, S)`: the minimum electrical energy of a unit flow from `v` to the set `S`
(footnote 7, p.29). -/
noncomputable def reffSet (c : V → V → ℝ) (v : V) (S : Finset V) : ℝ :=
  sInf {E | ∃ θ, IsUnitFlowToSet c θ v S ∧ E = MarkovMixing.flowEnergy c θ}

end IncrementalER


