-- Prove2me | Definitions.Def_SubSuperStoch_AsyncTrack_SignedDigraph
-- name    : SubSuperStoch_AsyncTrack_SignedDigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:27.868449+00:00
-- url     : https://prove2.me/theorems/7ca04d6a-8123-469c-8974-4b085c697739
-- title:
--   §2.3, pp. 12–13 — signed digraph with a leader, structural balance (C1), leader reachability (C2), directed distance d(v₀, v_i)
-- statement:
--   This file encodes the communication topology of §2.3: a network of one leader $v_0$ and $n$ followers $v_1,\dots,v_n$ connected by a signed digraph.
--
--   The followers exchange information along a signed digraph $\mathcal G$ with adjacency matrix $\mathcal A=[a_{ij}]\in\mathbb R^{n\times n}$: the edge $(v_j,v_i)$, from $v_j$ to $v_i$, is present exactly when $a_{ij}\neq 0$, and $a_{ij}>0$ ($a_{ij}<0$) means that $v_i$ receives cooperative (competitive) information from $v_j$. The number $a_{i0}$ describes the link from the leader to follower $v_i$: $a_{i0}\neq 0$ iff $v_i$ receives the leader's information, cooperatively if $a_{i0}>0$ and competitively if $a_{i0}<0$. The augmented digraph $\tilde{\mathcal G}$ consists of $\mathcal G$, the vertex $v_0$ and the leader edges $(v_0,v_i)$ with $a_{i0}\neq 0$.
--
--   1. **Condition C1 (structural balance).** The vertices of $\tilde{\mathcal G}$ split into two disjoint sets $\mathcal V_1\cup\mathcal V_2$ with $v_0\in\mathcal V_1$, such that
--   $$a_{ij}\ge 0 \text{ if } v_i,v_j \text{ lie in the same set},\qquad a_{ij}\le 0 \text{ if they lie in different sets},$$
--   for all $i\in\{1,\dots,n\}$ and $j\in\{0,1,\dots,n\}$. Writing $V_1$ for the followers in $\mathcal V_1$, the leader edges satisfy $a_{i0}\ge 0$ for $v_i\in V_1$ and $a_{i0}\le 0$ for $v_i\notin V_1$.
--   2. **Condition C2 (leader reachability).** For every follower $v_i$, $\tilde{\mathcal G}$ contains a directed path from the leader $v_0$ to $v_i$.
--   3. **Directed distance.** $d(v_0,v_i)$ is the number of edges of a shortest directed path from $v_0$ to $v_i$ in $\tilde{\mathcal G}$, the leader edge included. The predicate "$d(v_0,v_i)\le z$" holds when there is a walk $v_0\to v_{c_0}\to v_{c_1}\to\dots\to v_{c_m}=v_i$ with $m+1\le z$ edges.
--
--   C1 and C2 are the two conditions on the topology under which the paper proves bipartite tracking (Theorem 3.3); the largest distance $P=\max_i d(v_0,v_i)$ fixes the window length $Ph$ of Lemma 3.2.
--
--   **Formalization Note** Followers are `Fin n` with 0-based indices (index `i` is the paper's $v_{i+1}$); the leader is not an index. `a i j` is $a_{ij}$ and `b i` is $a_{i0}$. `StructBalanced a b V₁` is C1 for the partition $\mathcal V_1=\{v_0\}\cup V_1$, $\mathcal V_2=$ the other followers; placing the leader in $\mathcal V_1$ is the paper's "with no loss of generality" convention (p. 12). `LeaderReachable a b` is C2: some $j$ with $a_{j0}\neq 0$ from which $v_i$ is reached by follower edges `u → v` (`a v u ≠ 0`), possibly none. `reachWithin a b z i` says $d(v_0,v_i)\le z$; walks need not have distinct vertices, which does not change the length of a shortest one, so $d(v_0,v_i)$ is the least $z$ with `reachWithin a b z i`.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, pp. 12–13, §2.3 Signed digraph, conditions C1 and C2, and the convention 𝒱₁ = {v₀, v₁, …, v_m}

import Mathlib

namespace SubSuperStoch.AsyncTrack

/-!
The signed digraph of a leader `v₀` and `n` followers `v₁, …, vₙ` (§2.3, p. 12).
Followers are indexed by `Fin n` (0-based: index `i` is the paper's `v_{i+1}`); the leader is not an
index. The weights are `a : Matrix (Fin n) (Fin n) ℝ` (`a i j = a_ij`; the edge `v_j → v_i` is
present iff `a i j ≠ 0`) and `b : Fin n → ℝ` (`b i = a_i0`; the edge `v₀ → v_i` is present iff
`b i ≠ 0`).
-/

/-- Condition **C1** (p. 12): the signed digraph `𝒢̃` (followers and leader) is structurally
balanced, with the partition `𝒱₁ = {v₀} ∪ V₁`, `𝒱₂ = Fin n \ V₁` (the leader lies in `𝒱₁`, as
fixed on p. 12 "with no loss of generality"). Weights between vertices of the same subset are
`≥ 0`, weights between different subsets are `≤ 0`; for the leader edges this says `a_i0 ≥ 0` for
`v_i ∈ 𝒱₁` and `a_i0 ≤ 0` for `v_i ∈ 𝒱₂`. -/
def StructBalanced {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (V₁ : Set (Fin n)) :
    Prop :=
  (∀ i j, ((i ∈ V₁ ↔ j ∈ V₁) → 0 ≤ a i j) ∧ (¬(i ∈ V₁ ↔ j ∈ V₁) → a i j ≤ 0)) ∧
    ∀ i, (i ∈ V₁ → 0 ≤ b i) ∧ (i ∉ V₁ → b i ≤ 0)

/-- Condition **C2** (p. 12): for each follower `v_i`, `𝒢̃` contains a directed path from the
leader to `v_i`: an edge `v₀ → v_j` (`a_j0 ≠ 0`) followed by a (possibly empty) chain of follower
edges `u → v` (`a_vu ≠ 0`) from `v_j` to `v_i`. -/
def LeaderReachable {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Prop :=
  ∀ i, ∃ j, b j ≠ 0 ∧ Relation.ReflTransGen (fun u v => a v u ≠ 0) j i

/-- `reachWithin a b z i`: the directed distance `d(v₀, v_i)` (number of edges of a shortest path
from the leader to `v_i` in `𝒢̃`, p. 12) is at most `z`. Witness: a walk
`v₀ → c 0 → c 1 → ⋯ → c m = v_i` with `m + 1 ≤ z` edges (the leader edge `a_{c 0, 0} ≠ 0` and
`m` follower edges `a_{c(t+1), c(t)} ≠ 0`). A shortest walk has distinct vertices, so
`d(v₀, v_i)` is the least `z` with `reachWithin a b z i`. -/
def reachWithin {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (z : ℕ) (i : Fin n) :
    Prop :=
  ∃ m : ℕ, ∃ c : ℕ → Fin n,
    m + 1 ≤ z ∧ b (c 0) ≠ 0 ∧ c m = i ∧ ∀ t, t < m → a (c (t + 1)) (c t) ≠ 0

end SubSuperStoch.AsyncTrack


