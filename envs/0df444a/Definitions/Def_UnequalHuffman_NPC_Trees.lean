-- Prove2me | Definitions.Def_UnequalHuffman_NPC_Trees
-- name    : UnequalHuffman_NPC_Trees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:43:33.503075+00:00
-- url     : https://prove2.me/theorems/4d91ba1d-137d-41ae-b682-e34c6e59e6f6
-- title:
--   Finite ordered binary trees as prefix-closed word sets: leaves, full trees, depths, coordinates, leaf profiles, internal counts
-- statement:
--   A **rooted ordered binary tree** is a finite set $T$ of words over $\{0,1\}$ containing the empty word (the root) and closed under prefixes (`OTree`). The vertex $v$ has at most a left child $v0$ and a right child $v1$. A **leaf** is a vertex with no child, an **internal vertex** one with at least one child; $T$ is **full** if every internal vertex has both children. The **depth** of $v$ is its length, its **coordinate** the number of ones in it (the number of right edges on the root path).
--
--   `leafCount T t` and `internalCount T t` count the leaves and internal vertices at depth $t$. `leafCoords T t` is the list $z_{t,1}(T) \le \dots \le z_{t,n_t}(T)$ of the coordinates of the depth-$t$ leaves, sorted nondecreasingly with repetitions.
--
--   A **leaf profile** is a list $n = [n_1,\dots,n_H]$; `profileCount n t` is $n_t$ for $1 \le t \le H$ and $0$ otherwise. `IsProfileTree n T`: $T$ is full and has exactly $n_t$ leaves at every depth $t$ and no other leaves. The profile is **feasible** (`ProfileFeasible`) if such a tree exists. The **internal counts** are $I_0 = 1$, $I_t = 2I_{t-1} - n_t$ (`intCount`, integers). `codeTree C` is the tree of all prefixes of the codewords of a code $C$.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, pp. 7–9, §2.1 (trees, depth, coordinate), §2.2 (leaf profile, feasibility, internal counts)

import Mathlib

set_option autoImplicit false

namespace UnequalHuffman.NPC

/-- A finite rooted ordered binary tree, given by its vertices as words over `{0, 1}`
(`false` = left edge, label `0`; `true` = right edge, label `1`): the root is the empty word and
the set is closed under prefixes. Each vertex `v` has at most a left child `v ++ [false]` and a
right child `v ++ [true]`. -/
structure OTree where
  verts : Finset (List Bool)
  root_mem : [] ∈ verts
  prefix_closed : ∀ v ∈ verts, ∀ u, u <+: v → u ∈ verts

namespace OTree

/-- The leaves: vertices with no child. -/
def leaves (T : OTree) : Finset (List Bool) :=
  T.verts.filter fun v => v ++ [false] ∉ T.verts ∧ v ++ [true] ∉ T.verts

/-- The internal vertices: vertices with at least one child. -/
def internals (T : OTree) : Finset (List Bool) :=
  T.verts.filter fun v => v ++ [false] ∈ T.verts ∨ v ++ [true] ∈ T.verts

/-- The tree is full: every internal vertex has both children. -/
def IsFull (T : OTree) : Prop :=
  ∀ v ∈ T.verts, (v ++ [false] ∈ T.verts ↔ v ++ [true] ∈ T.verts)

/-- The number of leaves at depth `t` (depth = word length = number of edges from the root). -/
def leafCount (T : OTree) (t : ℕ) : ℕ :=
  (T.leaves.filter fun v => v.length = t).card

/-- The number of internal vertices at depth `t`. -/
def internalCount (T : OTree) (t : ℕ) : ℕ :=
  (T.internals.filter fun v => v.length = t).card

/-- The coordinates (numbers of right edges, `v.count true`) of the leaves at depth `t`, sorted
nondecreasingly with repetitions: `z_{t,1}(T) ≤ ⋯ ≤ z_{t,n_t}(T)` (list index `k - 1` holds the
rank-`k` coordinate). -/
def leafCoords (T : OTree) (t : ℕ) : List ℕ :=
  Multiset.sort (((T.leaves.filter fun v => v.length = t).val).map fun v => v.count true)

end OTree

/-- The prescribed number of leaves at depth `t` for the leaf profile `n = [n₁, …, n_H]`
(no leaves at depth `0` or beyond `H`). -/
def profileCount (n : List ℕ) (t : ℕ) : ℕ :=
  if t = 0 then 0 else n.getD (t - 1) 0

/-- `T` has exactly `n_t` leaves at every depth `t`, and no other leaves. -/
def HasProfile (T : OTree) (n : List ℕ) : Prop :=
  ∀ t, T.leafCount t = profileCount n t

/-- `T` is a full ordered binary tree with leaf profile `n`. -/
def IsProfileTree (n : List ℕ) (T : OTree) : Prop :=
  T.IsFull ∧ HasProfile T n

/-- A leaf profile is feasible if at least one full ordered binary tree has exactly those leaf
counts and no other leaves. -/
def ProfileFeasible (n : List ℕ) : Prop :=
  ∃ T : OTree, IsProfileTree n T

/-- The internal-count recurrence `I₀ = 1`, `I_t = 2 I_{t-1} - n_t` (in `ℤ`). -/
def intCount (n : List ℕ) : ℕ → ℤ
  | 0 => 1
  | t + 1 => 2 * intCount n t - (profileCount n (t + 1) : ℤ)

/-- The code tree of a code `C`: all prefixes of all codewords, together with the root. -/
def codeTree {m : ℕ} (C : Fin m → List Bool) : OTree where
  verts := insert [] (Finset.univ.biUnion fun i => (C i).inits.toFinset)
  root_mem := Finset.mem_insert_self _ _
  prefix_closed := by
    intro v hv u hu
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      List.mem_toFinset, List.mem_inits] at hv ⊢
    rcases hv with rfl | ⟨i, hi⟩
    · exact Or.inl (List.prefix_nil.mp hu)
    · exact Or.inr ⟨i, hu.trans hi⟩

end UnequalHuffman.NPC


