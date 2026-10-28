-- Prove2me | Definitions.Def_MmSChores_RoundRobin_Setting
-- name    : MmSChores_RoundRobin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:25:48.225237+00:00
-- url     : https://prove2.me/theorems/1d2a0aa3-5fc6-4269-bd3e-ef3aee74bb64
-- title:
--   Definition 1 and Algorithm 1 — chores instances, additive bundle values and the greedy round-robin run with arbitrary tie-breaking (pp. 2, 4)
-- statement:
--   This module sets up the objects of Theorem 9 of Aziz, Rauchecker, Schryen & Walsh.
--
--   1. **Instances** (Definition 1, p. 2). There are $N$ agents $[N]=\{1,\dots,N\}$ and a finite set $\mathcal M$ of $m$ items. Each agent $i$ has an additive utility function: $d_i(j)$ is her utility for item $j$, and the value of a bundle $S\subseteq\mathcal M$ is
--   $$d_i(S)=\sum_{j\in S} d_i(j).$$
--   2. **Chores instances** (Definition 1.2, p. 2). The instance is a chores instance if $d_i(j)\le 0$ for every agent $i$ and item $j$, and $d_i\not\equiv 0$ for every agent $i$, i.e. every agent has some item of nonzero utility. Items of a chores instance are called chores.
--   3. **Round-robin runs** (Algorithm 1, p. 4). In the greedy round-robin protocol the agents pick in rounds; in every round they pick in the order $1,2,\dots,N$, and at each pick the picker is given an item of highest utility *for her* among all items not yet picked. The picks are numbered $t=0,1,\dots,m-1$; pick $t$ is made by agent $(t \bmod N)+1$. A run is recorded as a bijection $\sigma$ from picks to items, $\sigma(t)$ being the item taken at pick $t$, subject to the greedy rule
--   $$d_i(\sigma(t'))\le d_i(\sigma(t))\qquad\text{whenever pick } t \text{ is made by agent } i \text{ and } t\le t'.$$
--   Ties are not resolved: every tie-breaking rule produces such a $\sigma$, and every such $\sigma$ arises from some tie-breaking rule.
--   4. **The allocation of a run.** Agent $i$'s bundle $S_i$ is the set of items taken at the picks she makes. The bundles $(S_1,\dots,S_N)$ are disjoint and cover $\mathcal M$; when $m<N$ some of them are empty.
--
--   The max-min share $\mathrm{MmS}^N_{d_i}(\mathcal M)$ of Definition 2.1 is the published definition `LittleCharity.MMS.mms`, applied to the bundle-value function $S\mapsto d_i(S)$.
--
--   **Formalization Note** Agents are `Fin N` and chores `Fin m`; the paper's agent $i$ is index $i-1$, so agent 1 is `0`. Utilities are `d : Fin N → Fin m → ℝ` and `bval d i S` is $d_i(S)$. `IsChores d` is the conjunction of `∀ i j, d i j ≤ 0` and `∀ i, ∃ j, d i j ≠ 0`; an additive function is identically zero exactly when every item is worth zero. `IsRoundRobinRun d σ` takes `σ : Fin m ≃ Fin m` and requires, for every agent `i` and picks `t ≤ t'` with `t % N = i`, that `d i (σ t') ≤ d i (σ t)`. `rrBundle σ i` is the set of chores `j` with `(σ.symm j) % N = i`. With `N = 0` the run condition is vacuous; every theorem using these objects assumes `0 < N`.
-- source:
--   Aziz, Rauchecker, Schryen & Walsh, Algorithms for Max-Min Share Fair Allocation of Indivisible Chores, AAAI 2017, PDF p. 2, Definition 1 (items 1–2); PDF p. 4, Algorithm 1 and the pick order in the proof of Theorem 9

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

namespace MmSChores.RoundRobin

open Finset

/-- The additive bundle value `d_i(S) = ∑_{j ∈ S} d_i(j)` of a set `S` of chores for agent `i`
(Definition 1, PDF p. 2: additive utility functions). Agents are `Fin N` (the paper's agent `i`
is index `i - 1`), chores are `Fin m`, and `d i j` is agent `i`'s utility for chore `j`. -/
def bval {N m : ℕ} (d : Fin N → Fin m → ℝ) (i : Fin N) (S : Finset (Fin m)) : ℝ :=
  ∑ j ∈ S, d i j

/-- A chores instance (Definition 1.2, PDF p. 2): `d_i(j) ≤ 0` for every agent `i` and chore `j`,
and `d_i ≢ 0` for every agent `i`. An additive utility is identically zero iff every chore is
worth `0` to it, so `d_i ≢ 0` is "some chore has nonzero utility for `i`". -/
def IsChores {N m : ℕ} (d : Fin N → Fin m → ℝ) : Prop :=
  (∀ i j, d i j ≤ 0) ∧ ∀ i, ∃ j, d i j ≠ 0

/-- A run of the greedy round-robin protocol (Algorithm 1, PDF p. 4), under some tie-breaking
rule. The picks are numbered `t = 0, 1, …, m - 1`; pick `t` is made by agent `t mod N`, so in
every round the agents pick in the order `0, 1, …, N - 1`. `σ t` is the chore taken at pick `t`;
`σ` is a bijection, so every chore is taken exactly once. The greedy rule: when agent `i` makes
pick `t`, the chore she takes has, for her, the highest utility among all remaining chores, i.e.
among the chores taken at picks `t' ≥ t`. Ties may be broken arbitrarily. -/
def IsRoundRobinRun {N m : ℕ} (d : Fin N → Fin m → ℝ) (σ : Fin m ≃ Fin m) : Prop :=
  ∀ (i : Fin N) (t t' : Fin m), (t : ℕ) % N = i → t ≤ t' → d i (σ t') ≤ d i (σ t)

/-- The bundle `S_i` of agent `i` in the allocation produced by the run `σ`: the chores taken at
the picks made by `i`, i.e. at the picks `t` with `t mod N = i`. -/
def rrBundle {N m : ℕ} (σ : Fin m ≃ Fin m) (i : Fin N) : Finset (Fin m) :=
  univ.filter (fun j => ((σ.symm j : ℕ) % N) = i)

end MmSChores.RoundRobin


