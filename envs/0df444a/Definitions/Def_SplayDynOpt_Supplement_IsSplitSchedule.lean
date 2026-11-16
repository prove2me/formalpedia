-- Prove2me | Definitions.Def_SplayDynOpt_Supplement_IsSplitSchedule
-- name    : SplayDynOpt_Supplement_IsSplitSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:08:28.5666+00:00
-- url     : https://prove2.me/theorems/14830348-22cc-4d33-a9f7-02722aeae014
-- title:
--   Normal-form forest schedules for a sequence of splits
-- statement:
--   Fix constants $k\in\mathbb N$ and $C\in\mathbb R$, an integer $n$ and a sequence $x_1,\dots,x_n$ (a permutation of $[n]=\{1,\dots,n\}$ in Theorem 47). A **binary search tree on a sub-interval of $[n]$** is a binary search tree whose key set is $\{a,a+1,\dots,b\}$ for some $1\le a\le b\le n$; in particular it is nonempty.
--
--   A **normal-form forest schedule** for $x_1,\dots,x_n$ consists of forests $\mathcal F_0,\mathcal F_1,\dots,\mathcal F_\ell$ (finite sets of binary trees) and times $1\le t_1<\dots<t_n\le\ell$ such that
--
--   1. $\mathcal F_0=\{T_0\}$ for a binary search tree $T_0$ on $[n]$;
--   2. for every $1\le i\le\ell$ and every $T\in\mathcal F_i$, $T$ is a binary search tree on a sub-interval of $[n]$, $T$ is $k$-ribless, and the depth of $T$ (the number of edges on a longest root-to-node path) is at most $C\log_2|T|$, where $|T|$ is the number of keys of $T$;
--   3. $\mathcal F_\ell$ consists of $n$ one-node trees;
--   4. for every $1\le i\le\ell$ that is not one of $t_1,\dots,t_n$, $\mathcal F_{i-1}\setminus\mathcal F_i=\{T\}$ and $\mathcal F_i\setminus\mathcal F_{i-1}=\{T'\}$, where $T'$ is obtained from $T$ by one rotation of a key of depth at most $k$ in $T$;
--   5. for every $j$, either $\mathcal F_{t_j-1}=\mathcal F_{t_j}$ and the one-node tree $x_j$ belongs to $\mathcal F_{t_j-1}$, or $\mathcal F_{t_j-1}\setminus\mathcal F_{t_j}=\{T\}$ and $\mathcal F_{t_j}\setminus\mathcal F_{t_j-1}=\{T_L,T_x,T_R\}$, where $T$ has root $x_j$, $T_L$ and $T_R$ are its left and right subtrees, $T_x$ is the one-node tree $x_j$, and an empty $T_L$ or $T_R$ is left out.
--
--   This is the shape of the optimal forest that Theorem 47 provides for the split conjecture: every tree stays ribless and of logarithmic depth, rotations happen only near a root, and each split cuts a tree at its root.
--
--   **Formalization Note** Forests are `Finset (BinaryTree ℕ)`. Mathlib's `height` counts nodes, so the depth bound reads $\mathrm{height}(T)\le C\log_2|T|+1$; a one-node tree has depth $0$. One constant $k$ bounds both the rib sizes (the published `kRibless`) and the rotation depth (the published `IsRotationWithin`). The times are indexed from $0$ in Lean: `t j` is the time of $x_{j+1}$.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 47, p.76 (App. C.6)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_rotateAt
import Definitions.Def_SplayDynOpt_kRibless

set_option autoImplicit false

namespace SplayDynOpt.Supplement

open BinaryTree SplayDynOpt

/-- `T` is a **binary search tree on a sub-interval of `[n]`**: it has the ordering property and
its key set is `{a, a+1, …, b}` for some `1 ≤ a ≤ b ≤ n` (so `T` is nonempty).

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), Theorem 47,
p.76, item 2: "T is a binary search tree on a sub-interval of [n]". -/
def IsBSTOnInterval (n : ℕ) (T : BinaryTree ℕ) : Prop :=
  IsBST T ∧ ∃ a b : ℕ, 1 ≤ a ∧ a ≤ b ∧ b ≤ n ∧ keys T = Finset.Icc a b

/-- A **normal-form forest schedule for the split sequence** `xs = x₁, …, x_n` with constants
`k` (riblessness and rotation depth) and `C` (depth): forests `F 0, F 1, …, F ℓ` (finite sets of
binary trees) and times `t 0 < t 1 < ⋯ < t (n-1)` in `{1, …, ℓ}` (`t j` is the time of the split
of `x_{j+1}`), such that

1. `F 0` consists of a single binary search tree on `[n]`;
2. for every `1 ≤ i ≤ ℓ` and every `T ∈ F i`, `T` is a binary search tree on a sub-interval of
   `[n]`, `T` is `k`-ribless and its depth (edges on a longest root-to-node path, i.e.
   `height T - 1`) is at most `C · log₂ |T|`;
3. `F ℓ` consists of `n` singleton binary search trees;
4. for every `1 ≤ i ≤ ℓ` that is not a split time, `F (i-1) \ F i = {T}` and
   `F i \ F (i-1) = {T'}`, where `T'` is obtained from `T` by a single rotation of a key of depth
   at most `k`;
5. for every `j`, with `x = x_{j+1}` and `s = t j`: either `F (s-1) = F s` and the singleton tree
   `x` belongs to `F (s-1)`, or `F (s-1) \ F s = {T}` and `F s \ F (s-1) = {T_L, T_x, T_R}`, where
   `T` has root `x`, `T_L`, `T_R` are its left and right subtrees and `T_x` is the one-node tree
   `x`; an empty `T_L` or `T_R` is omitted.

Chmel et al., Theorem 47, p.76 (App. C.6).

**Formalization Note.** Forests are `Finset (BinaryTree ℕ)` and `\` is set difference, as printed.
`|T|` is the number of keys of `T`. Mathlib's `BinaryTree.height` counts nodes (a one-node tree has
height `1`), so the paper's depth, which counts edges (a singleton has depth `0`), is `height T - 1`
and item 2 reads `height T ≤ C · log₂ |T| + 1`. One constant `k` serves both "ribless"
(`kRibless k`, App. C.1, p.61) and "a single rotation at depth at most O(1)" (`IsRotationWithin k`);
this loses nothing, since both properties are monotone in `k`. Items 2 and 4 are for
`i ∈ [ℓ] = {1, …, ℓ}`, as printed. The empty tree is omitted from item 5's new trees by filtering
out `nil`. Split times are indexed from `0`: `t j` is the time of `xs[j]`, i.e. of `x_{j+1}`. -/
def IsSplitSchedule (k : ℕ) (C : ℝ) (n : ℕ) (xs : List ℕ) (ℓ : ℕ)
    (F : ℕ → Finset (BinaryTree ℕ)) (t : ℕ → ℕ) : Prop :=
  -- times t₁ < ⋯ < tₙ in [ℓ]
  (∀ j, j < n → 1 ≤ t j ∧ t j ≤ ℓ) ∧
  (∀ j j', j < j' → j' < n → t j < t j') ∧
  -- 1. F₀ is a single BST on [n]
  (∃ T₀ : BinaryTree ℕ, IsBSTOn n T₀ ∧ F 0 = {T₀}) ∧
  -- 2. trees of F₁, …, F_ℓ: BST on a sub-interval, k-ribless, depth ≤ C · log₂ |T|
  (∀ i, 1 ≤ i → i ≤ ℓ → ∀ T ∈ F i,
    IsBSTOnInterval n T ∧ kRibless k T ∧
      (T.height : ℝ) ≤ C * Real.logb 2 ((keys T).card : ℝ) + 1) ∧
  -- 3. F_ℓ consists of n singleton trees
  ((F ℓ).card = n ∧ ∀ T ∈ F ℓ, ∃ x : ℕ, T = node x nil nil) ∧
  -- 4. non-split steps: one tree replaced by a rotation of it at depth ≤ k
  (∀ i, 1 ≤ i → i ≤ ℓ → (∀ j, j < n → t j ≠ i) →
    ∃ T T' : BinaryTree ℕ, F (i - 1) \ F i = {T} ∧ F i \ F (i - 1) = {T'} ∧
      IsRotationWithin k T T') ∧
  -- 5. split steps
  (∀ j x, xs[j]? = some x →
    (F (t j - 1) = F (t j) ∧ node x nil nil ∈ F (t j - 1)) ∨
    (∃ L R : BinaryTree ℕ, F (t j - 1) \ F (t j) = {node x L R} ∧
      F (t j) \ F (t j - 1) = ({L, node x nil nil, R} : Finset (BinaryTree ℕ)).filter (· ≠ nil)))

end SplayDynOpt.Supplement


