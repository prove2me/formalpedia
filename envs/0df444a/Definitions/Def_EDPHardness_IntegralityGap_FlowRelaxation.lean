-- Prove2me | Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
-- name    : EDPHardness_IntegralityGap_FlowRelaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:16.659979+00:00
-- url     : https://prove2.me/theorems/524b86df-b444-4dfe-b887-09f6e424fbad
-- title:
--   §2.1 — the multicommodity flow relaxation of EDP and integral routings with congestion at most c − 1
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph and let $(s_i,t_i)$, $i\in I$, be a finite family of source–sink pairs. For each pair let $\mathcal P^{(i)}$ be the set of paths of $G$ joining $s_i$ and $t_i$.
--
--   1. A **feasible fractional solution** of the multicommodity flow relaxation assigns to every path $P\in\mathcal P^{(i)}$ an amount of flow $f(P)\in[0,1]$, nonzero on finitely many paths, and to every pair the routed flow $x_i=\sum_{P\in\mathcal P^{(i)}} f(P)$, subject to $x_i\in[0,1]$ and to the edge capacities
--   $$\sum_{i\in I}\ \sum_{P\in\mathcal P^{(i)}:\ e\in P} f(P)\le 1\qquad\text{for every edge } e\in E.$$
--   Its **value** is $|\bar f|=\sum_{i} x_i$. This is the LP
--   $$\max \sum_i x_i \quad\text{s.t.}\quad x_i-\sum_{P\in\mathcal P^{(i)}} f(P)=0,\qquad \sum_{P:\,e\in P} f(P)\le 1,\qquad x_i,f(P)\in[0,1].$$
--   2. An **integral routing with congestion at most $\kappa$** chooses a set $R\subseteq I$ of routed pairs and, for every $i\in R$, an $s_i$–$t_i$ path $\pi_i$ of $G$, such that every edge of $G$ lies on at most $\kappa$ of the paths $\pi_i$. Its value is $|R|$, the number of routed pairs.
--
--   In the integrality-gap statements of the paper the fractional solution obeys the capacity-$1$ constraints above, while the integral solution may route up to $c-1$ paths through every edge ($\kappa=c-1$).
--
--   **Formalization Note** The fractional solution stores, for each pair, a finite set of $s_i$–$t_i$ walks that are paths (`IsPath`), and the weights $f$ on them; variables of paths outside this set are $0$. Edges are unordered pairs (`Sym2 V`); the capacity constraint is imposed for every unordered pair, which is no restriction because a path only contains edges of $G$. The integral routing stores a path only for the routed pairs.
-- source:
--   Andrews, Chuzhoy, Guruswami, Khanna, Talwar, Zhang, Inapproximability of Edge-Disjoint Paths and Low Congestion Routing on Undirected Graphs, Combinatorica 30 (2010), pp. 491–492, Section 2.1 (the LP relaxation and the congestion-(c−1) integral solutions)

import Mathlib

namespace EDPHardness.IntegralityGap

/-- A feasible solution of the multicommodity flow relaxation of EDP (Andrews et al. 2010,
§2.1, p. 492) on a simple graph `G` with source–sink pairs `(s i, t i)`, `i : ι`.
Every pair `i` carries a finite set `paths i` of `s i`–`t i` paths of `G` (the support of the
path variables of `𝒫^{(i)}`; variables outside it are `0`), with weights `f i P ∈ [0, 1]`.
The flow routed for pair `i` is `x i = ∑_{P ∈ paths i} f i P`, which must lie in `[0, 1]`,
and every edge carries total flow at most `1`. -/
structure FracSol {V : Type*} [DecidableEq V] (G : SimpleGraph V) {ι : Type*} [Fintype ι]
    (s t : ι → V) where
  /-- The paths of `𝒫^{(i)}` that carry flow. -/
  paths : (i : ι) → Finset (G.Walk (s i) (t i))
  /-- The path variables `f(P)`. -/
  f : (i : ι) → G.Walk (s i) (t i) → ℝ
  /-- Every flow-carrying walk is a path. -/
  isPath : ∀ i, ∀ P ∈ paths i, P.IsPath
  /-- `f(P) ≥ 0`. -/
  f_nonneg : ∀ i, ∀ P ∈ paths i, 0 ≤ f i P
  /-- `f(P) ≤ 1`. -/
  f_le_one : ∀ i, ∀ P ∈ paths i, f i P ≤ 1
  /-- `x_i = ∑_{P ∈ 𝒫^{(i)}} f(P) ≤ 1` (and `x_i ≥ 0` follows from `f ≥ 0`). -/
  x_le_one : ∀ i, ∑ P ∈ paths i, f i P ≤ 1
  /-- Edge capacity: `∑_{P : e ∈ P} f(P) ≤ 1` for every edge `e`. -/
  capacity : ∀ e : Sym2 V,
    ∑ i, ∑ P ∈ (paths i).filter (fun P => e ∈ P.edges), f i P ≤ 1

namespace FracSol

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {ι : Type*} [Fintype ι] {s t : ι → V}

/-- The flow `x_i` routed for pair `i`. -/
def x (F : FracSol G s t) (i : ι) : ℝ := ∑ P ∈ F.paths i, F.f i P

/-- The objective value `|f̄| = ∑_i x_i`. -/
def value (F : FracSol G s t) : ℝ := ∑ i, F.x i

end FracSol

/-- An integral routing with congestion at most `cong` (Andrews et al. 2010, §2.1, p. 492:
"allow the integral solution to route up to (c−1) paths through any edge e", with
`cong = c − 1`): a set `routed` of pairs, each routed on an `s i`–`t i` path of `G`, such that
every edge lies on at most `cong` of the chosen paths. Its value is `routed.card`. -/
structure IntRouting {V : Type*} [DecidableEq V] (G : SimpleGraph V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s t : ι → V) (cong : ℕ) where
  /-- The pairs that are routed. -/
  routed : Finset ι
  /-- The path chosen for each routed pair. -/
  path : (i : routed) → G.Walk (s i) (t i)
  /-- Each chosen walk is a path. -/
  isPath : ∀ i, (path i).IsPath
  /-- Every edge lies on at most `cong` chosen paths. -/
  congestion : ∀ e : Sym2 V,
    (Finset.univ.filter (fun i : routed => e ∈ (path i).edges)).card ≤ cong

end EDPHardness.IntegralityGap


