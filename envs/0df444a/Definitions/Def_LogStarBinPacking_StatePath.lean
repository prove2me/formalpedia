-- Prove2me | Definitions.Def_LogStarBinPacking_StatePath
-- name    : LogStarBinPacking_StatePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:22.965731+00:00
-- url     : https://prove2.me/theorems/1644e44d-233d-48d1-9a98-e155e2f9121e
-- title:
--   State paths $P(I,V,h)$, feasible weight families and disjoint path partitions
-- statement:
--   Let $I$ be a bin packing instance with $n=|I|$ items and sizes $s_I(i)\in(0,1]$, let $V$ be a finite set of **states** and $h:V\to[0,1]\cap\mathbb Q$ a load function. A **state path** is a sequence
--   $$
--   \pi=(v_0,i_1,v_1,\dots,i_k,v_k),\qquad 0\le k\le n,
--   $$
--   with pairwise distinct states $v_0,\dots,v_k\in V$, pairwise distinct items $i_1,\dots,i_k\in I$, and
--   $$
--   h(v_j)\ \ge\ h(v_{j-1})+s_I(i_j)\qquad(1\le j\le k).
--   $$
--   Write $V(\pi)=\{v_0,\dots,v_k\}$, $I(\pi)=\{i_1,\dots,i_k\}$, and $P(I,V,h)$ for the (finite) set of state paths. Two paths are **disjoint** if they share no state and no item.
--
--   1. Nonnegative weights $x=(x_\pi)_{\pi\in P}$ are a **feasible weight family** for $(I,b,V,h)$ if $\sum_\pi x_\pi=b$, $\sum_{\pi:\,i\in I(\pi)}x_\pi=1$ for every item $i$, and $\sum_{\pi:\,v\in V(\pi)}x_\pi\le1$ for every state $v$.
--   2. A family $\pi_1,\dots,\pi_b$ is a **disjoint path partition** of $I$ if the paths are pairwise disjoint and their item sets cover $I$.
--
--   A state path describes the items of one source bin in the order of insertion, with $h$ bounding the partial loads; these are the objects the three-item reduction encodes.
--
--   **Formalization Note** A path is its length $k\in\{0,\dots,n\}$ with injective maps $\mathrm{Fin}(k+1)\hookrightarrow V$ and $\mathrm{Fin}\,k\hookrightarrow I$ (0-based). Weights are real. The range condition on $h$ is a hypothesis of each theorem. A block $I(\pi_j)$ of a disjoint path partition may be empty.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), §2.1, (2.1)–(2.2), pp.3–4; Lemma 2.1(ii), p.4

import Mathlib
import Definitions.Def_BinPackingGap

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **State paths `P(I, V, h)`.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three
Items per Bin*, manuscript (sha256 1d88425d…), §2.1, (2.1), pp.3–4. For a bin packing instance `I`
with `n = |I|` items, a finite set of states `V` and a load function `h : V → [0, 1] ∩ ℚ`, a state
path is a sequence `π = (v₀, i₁, v₁, …, i_k, v_k)` with `0 ≤ k ≤ n`, pairwise distinct states
`v₀, …, v_k ∈ V`, pairwise distinct items `i₁, …, i_k ∈ I`, and
`h(v_j) ≥ h(v_{j−1}) + s_I(i_j)` for `1 ≤ j ≤ k` (2.1).

**Formalization Note** A path is the length `k ∈ {0, …, n}` (a `Fin (n + 1)`), an injective map
`Fin (k + 1) ↪ V` (the states `v₀, …, v_k`, so `v_j` is index `j`) and an injective map
`Fin k ↪ I.Item` (the items `i₁, …, i_k`, so `i_j` is index `j − 1`). Condition (2.1) for step
`j` reads `h (state j.castSucc) + s_I (item j) ≤ h (state j.succ)`. The range `h(V) ⊆ [0, 1]` is a
hypothesis of each theorem. The set of paths is a finite type. -/
def StatePath (I : Instance) (V : Type*) [Fintype V] [DecidableEq V] (h : V → ℚ) : Type _ :=
  Σ k : Fin (I.n + 1), {p : (Fin (k.val + 1) ↪ V) × (Fin k.val ↪ I.Item) //
    ∀ j : Fin k.val, h (p.1 j.castSucc) + I.size (p.2 j) ≤ h (p.1 j.succ)}

namespace StatePath

variable {I : Instance} {V : Type*} [Fintype V] [DecidableEq V] {h : V → ℚ}

noncomputable instance instFintype : Fintype (StatePath I V h) := by
  unfold StatePath
  infer_instance

/-- The number `k` of items of the path. -/
def len (π : StatePath I V h) : ℕ := π.1.val

/-- The `j`-th state `v_j`, `0 ≤ j ≤ k`. -/
def state (π : StatePath I V h) : Fin (π.len + 1) ↪ V := π.2.val.1

/-- The `j`-th item `i_{j+1}`, `0 ≤ j < k`. -/
def item (π : StatePath I V h) : Fin π.len ↪ I.Item := π.2.val.2

/-- The state set `V(π) = {v₀, …, v_k}`. -/
def stateSet (π : StatePath I V h) : Finset V := Finset.univ.map π.state

/-- The item set `I(π) = {i₁, …, i_k}`. -/
def itemSet (π : StatePath I V h) : Finset I.Item := Finset.univ.map π.item

/-- The initial state `v₀`. -/
def first (π : StatePath I V h) : V := π.state 0

/-- The final state `v_k`. -/
def last (π : StatePath I V h) : V := π.state (Fin.last π.len)

/-- Two state paths are disjoint if they share no state and no item. -/
def Disjoint' (π π' : StatePath I V h) : Prop :=
  Disjoint π.stateSet π'.stateSet ∧ Disjoint π.itemSet π'.itemSet

end StatePath

/-- **Feasible weight family (2.2).** Doron-Arad, manuscript (sha256 1d88425d…), (2.2), p.4:
nonnegative weights `x = (x_π)_{π ∈ P}` are feasible for `(I, b, V, h)` if
`∑_{π ∈ P} x_π = b`, `∑_{π ∈ P, i ∈ I(π)} x_π = 1` for every `i ∈ I`, and
`∑_{π ∈ P, v ∈ V(π)} x_π ≤ 1` for every `v ∈ V`.

**Formalization Note** Weights are real. -/
def IsFeasibleWeightFamily (I : Instance) (b : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (h : V → ℚ) (x : StatePath I V h → ℝ) : Prop :=
  (∀ π, 0 ≤ x π) ∧
  (∑ π, x π = (b : ℝ)) ∧
  (∀ i : I.Item, ∑ π ∈ Finset.univ.filter (fun π : StatePath I V h => i ∈ π.itemSet), x π = 1) ∧
  (∀ v : V, ∑ π ∈ Finset.univ.filter (fun π : StatePath I V h => v ∈ π.stateSet), x π ≤ 1)

/-- There exists a feasible weight family for `(I, b, V, h)` (Doron-Arad, manuscript, (2.2), p.4). -/
def HasFeasibleWeightFamily (I : Instance) (b : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (h : V → ℚ) : Prop :=
  ∃ x : StatePath I V h → ℝ, IsFeasibleWeightFamily I b h x

/-- **Disjoint paths partitioning the items.** Doron-Arad, manuscript (sha256 1d88425d…), Lemma
2.1(ii), p.4: `π₁, …, π_b ∈ P(I, V, h)` are pairwise disjoint (no shared state or item) and
`I(π₁), …, I(π_b)` is a partition of `I`.

**Formalization Note** "Partition" is read as: the sets `I(π_j)` are pairwise disjoint (already
part of path disjointness) and cover `I`; an empty `I(π_j)` is allowed. -/
def IsDisjointPathPartition (I : Instance) {V : Type*} [Fintype V] [DecidableEq V]
    (h : V → ℚ) {b : ℕ} (π : Fin b → StatePath I V h) : Prop :=
  (∀ j j' : Fin b, j ≠ j' → (π j).Disjoint' (π j')) ∧
  (∀ i : I.Item, ∃ j : Fin b, i ∈ (π j).itemSet)

end LogStarBinPacking


