-- Prove2me | Definitions.Def_TreeEdgeRankPC_CriticalSet
-- name    : TreeEdgeRankPC_CriticalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:07.045509+00:00
-- url     : https://prove2.me/theorems/5c548aa6-8246-4b7c-af8d-5b39525c2ffe
-- title:
--   Visible sets, weight, critical sets, $\kappa$, subtrees, branches, realizability and $\mathrm{CR}$
-- statement:
--   Let $T$ be a tree rooted at $r$. For an edge ranking $\rho$, a rank is **visible** from the root if some edge with that rank has no edge of larger rank on its path to the root; the **visible set** is the set of visible ranks. The **weight** of a set $A$ of ranks is
--   $$\mathrm{wt}(A)=\sum_{a\in A}2^{a-1}.$$
--   The **critical set** $\mathrm{crit}(T)$ is the unique visible set of minimum weight over all edge rankings of $T$, and a ranking whose visible set is critical is a **critical ranking**.
--
--   For a vertex $v$, $T_v$ is the subtree consisting of $v$ and its descendants, and **branch** $i$ at $v$ is the edge $vv_i$ together with $T_{v_i}$, for a child $v_i$. With a visible set $A_i$ fixed for $T_{v_i}$, a rank $c$ is **admissible** for branch $i$ when $c\notin A_i$, and the branch then contributes
--   $$\kappa(A_i,c)=\{c\}\cup\{x\in A_i: x>c\}$$
--   to the visible set at $v$. An assignment of admissible ranks is **critical** if it gives a valid ranking whose visible set $\bigcup_i\kappa(A_i,c_i)$ has minimum weight among all valid assignments; $\mathrm{CR}(A_1,\dots,A_d)$ is the visible set of a critical assignment. A set $X$ of ranks is **realizable** for a rooted tree if the tree admits a valid edge ranking whose visible set is contained in $X$.
--
--   These notions organize a tree's edge rankings by what a parent edge can see, and they turn the root of a tree into an allocation problem over bits.
--
--   **Formalization Note** Sets of ranks are finite sets of positive integers (`IsRankSet`), and `wt` is injective on them. `crit` and `CR` are chosen by `Classical.epsilon`; a critical set exists and is unique for a finite tree (proved in the mission's verification file). `subtree` and `branch` are graphs on the same vertex type with all other vertices isolated: rankings, visibility and critical sets depend only on edges and on walks from the root, so nothing changes from the induced subtree. A valid assignment is stated through the criterion of Proposition 3.2 (positive admissible ranks, pairwise disjoint $\kappa$ sets), itself a milestone.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.1, pp.10–11 (eq. (3.1)); §4.1, p.15 (realizable)

import Mathlib
import Definitions.Def_TreeEdgeRankPC_EdgeRanking

open Classical

namespace TreeEdgeRankPC

/-- A **set of ranks**: a finite set of positive integers. -/
def IsRankSet (A : Finset ℕ) : Prop := ∀ a ∈ A, 1 ≤ a

/-- **Weight** of a set of ranks, §3.1, p.10 (arXiv:2610.12438, held version of 2026-11-02, sha256
9e04ca7b…): `wt(A) = Σ_{a∈A} 2^{a−1}`.

**Formalization Note.** Used only on sets of positive ranks (`IsRankSet`), where the natural-number
subtraction `a - 1` is exact and `wt` is injective. -/
def wt (A : Finset ℕ) : ℕ := ∑ a ∈ A, 2 ^ (a - 1)

/-- The **visible set** of `ρ` from the root `r`, §3.1, p.10: "a rank r is visible from the root if some
edge with rank r has no edge of larger rank on its path to the root ... The visible set of an edge
ranking is the set of ranks that are visible from the root."

**Formalization Note.** The path of an edge `e` to the root is the path from `r` to an endpoint of
`e` that contains `e` (in a tree it is unique: it ends at the endpoint of `e` farther from `r`). Only
edges of `T` are considered, so `visible` depends only on the values of `ρ` on `T.edgeSet`. -/
noncomputable def visible {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V) (ρ : Sym2 V → ℕ) :
    Finset ℕ :=
  (Finset.univ.filter fun e : Sym2 V => e ∈ T.edgeSet ∧
    ∃ (x : V) (p : T.Walk r x), p.IsPath ∧ x ∈ e ∧ e ∈ p.edges ∧ ∀ g ∈ p.edges, ρ g ≤ ρ e).image ρ

/-- `C` is a **critical set** of the tree `T` rooted at `r`: it is the visible set of a valid edge
ranking and has minimum weight among all such visible sets (§3.1, p.10). -/
def IsCriticalSet {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V) (C : Finset ℕ) : Prop :=
  (∃ ρ, IsEdgeRanking T ρ ∧ visible T r ρ = C) ∧
    ∀ ρ, IsEdgeRanking T ρ → wt C ≤ wt (visible T r ρ)

/-- The **critical set** `crit(T)`, §3.1, p.10 (arXiv:2610.12438, held version of 2026-11-02, sha256
9e04ca7b…): "The critical set crit(T) is the unique visible set of minimum weight over all edge
rankings of T."

**Formalization Note.** Chosen by `Classical.epsilon`. For a finite tree a critical set exists, and
it is unique because `wt` is injective on sets of positive ranks; the mission's verification file
proves both, so the choice is exactly that set. -/
noncomputable def crit {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V) : Finset ℕ :=
  Classical.epsilon (IsCriticalSet T r)

/-- A ranking is a **critical ranking** when it is valid and its visible set is critical (§3.1, p.10). -/
def IsCriticalRanking {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V) (ρ : Sym2 V → ℕ) : Prop :=
  IsEdgeRanking T ρ ∧ visible T r ρ = crit T r

/-- `κ(A, c) = {c} ∪ {x ∈ A : x > c}`, eq. (3.1), §3.1, p.11 (arXiv:2610.12438, held version of
2026-11-02, sha256 9e04ca7b…): what a branch with rank `c` contributes to the visible set at its
parent, when its child's visible set is `A`. -/
def kappa (A : Finset ℕ) (c : ℕ) : Finset ℕ := insert c (A.filter (c < ·))

/-- **Realizability**, §4.1, p.15: "a set of ranks X is realizable for a rooted tree if the tree admits
a valid edge ranking whose visible set is contained in X." -/
def Realizable {V : Type*} [Fintype V] (T : SimpleGraph V) (r : V) (X : Finset ℕ) : Prop :=
  ∃ ρ, IsEdgeRanking T ρ ∧ visible T r ρ ⊆ X

/-- The vertices of the subtree `T_v` of the tree `T` rooted at `r`, §3.1, p.10: "`T_v` denote[s] the
subtree rooted at v consisting of v and its descendants". A vertex `x` belongs to it when the path
from `r` to `x` passes through `v`. -/
def descendants {V : Type*} (T : SimpleGraph V) (r v : V) : Set V :=
  {x | ∃ p : T.Walk r x, p.IsPath ∧ v ∈ p.support}

/-- The **children** of `v` in the tree `T` rooted at `r`: the neighbours of `v` farther from `r`. -/
noncomputable def children {V : Type*} [Fintype V] (T : SimpleGraph V) (r v : V) : Finset V :=
  Finset.univ.filter fun c => T.Adj v c ∧ T.dist r c = T.dist r v + 1

/-- The subtree **`T_v`** of `T` rooted at `r`, §3.1, p.10.

**Formalization Note.** It is the graph on the same vertex type `V` whose edges are the edges of `T`
with both endpoints in `descendants T r v`, rooted at `v`. Vertices outside `T_v` are isolated. Every
notion in this mission (`IsEdgeRanking`, `er`, `visible`, `crit`) depends only on the edges and on
walks from the root, so this graph has the same rankings, visible sets and critical set as the
induced subtree on `descendants T r v`. It avoids nested subtypes. -/
def subtree {V : Type*} (T : SimpleGraph V) (r v : V) : SimpleGraph V where
  Adj a b := T.Adj a b ∧ a ∈ descendants T r v ∧ b ∈ descendants T r v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => T.loopless.irrefl _ h.1⟩

/-- **Branch** `c` at the root `v` of the tree `T`, §3.1, p.11 and §4.1, p.15: "the edge vv_i together
with the subtree T_{v_i}", rooted at `v` ("each including its edge incident to v and rooted at v").

**Formalization Note.** As with `subtree`, a graph on the same vertex type `V`, with every vertex
outside the branch isolated. Here `T` is rooted at `v`, and `c` is a child of `v`. -/
def branch {V : Type*} (T : SimpleGraph V) (v c : V) : SimpleGraph V where
  Adj a b := T.Adj a b ∧ (s(a, b) = s(v, c) ∨ (a ∈ descendants T v c ∧ b ∈ descendants T v c))
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h' | h'
    · exact Or.inl (by rw [Sym2.eq_swap]; exact h')
    · exact Or.inr ⟨h'.2, h'.1⟩⟩⟩
  loopless := ⟨fun _ h => T.loopless.irrefl _ h.1⟩

/-- An assignment of ranks `c i` to the branches `i ∈ D`, with child visible sets `A i`, in which every
rank is positive and admissible (`c i ∉ A i`, §3.1, p.11) and the sets `κ(A i, c i)` are pairwise
disjoint. By Proposition 3.2 (p.11) these are exactly the assignments that give a valid ranking. -/
def ValidAssignment {ι : Type*} (D : Finset ι) (A : ι → Finset ℕ) (c : ι → ℕ) : Prop :=
  (∀ i ∈ D, 1 ≤ c i ∧ c i ∉ A i) ∧
    (D : Set ι).PairwiseDisjoint fun i => kappa (A i) (c i)

/-- The visible set `⋃_i κ(A i, c i)` of an assignment, §3.1, p.11. -/
def assignmentSet {ι : Type*} (D : Finset ι) (A : ι → Finset ℕ) (c : ι → ℕ) : Finset ℕ :=
  D.biUnion fun i => kappa (A i) (c i)

/-- A **critical assignment**, §3.1, p.11: "An assignment of admissible ranks c1, ..., cd to the branches
is critical if it gives a ranking of T_v that is valid and whose visible set ⋃ κ(A_i, c_i) has minimum
weight among all valid assignments."

**Formalization Note.** "Gives a valid ranking" is stated through the criterion of Proposition 3.2,
which is a milestone of this mission. -/
def IsCriticalAssignment {ι : Type*} (D : Finset ι) (A : ι → Finset ℕ) (c : ι → ℕ) : Prop :=
  ValidAssignment D A c ∧
    ∀ c', ValidAssignment D A c' → wt (assignmentSet D A c) ≤ wt (assignmentSet D A c')

/-- **`CR(A₁, ..., A_d)`**, §3.1, p.11: "We denote the visible set of a critical assignment by
CR(A1, ..., Ad)."

**Formalization Note.** Chosen by `Classical.epsilon`. A critical assignment always exists (large
distinct ranks are valid, and weights are natural numbers), and on sets of positive ranks all critical
assignments have the same visible set because `wt` is injective. -/
noncomputable def CR {ι : Type*} (D : Finset ι) (A : ι → Finset ℕ) : Finset ℕ :=
  Classical.epsilon fun S => ∃ c, IsCriticalAssignment D A c ∧ S = assignmentSet D A c

end TreeEdgeRankPC


