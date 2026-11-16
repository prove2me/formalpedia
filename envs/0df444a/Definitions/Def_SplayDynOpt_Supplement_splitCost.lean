-- Prove2me | Definitions.Def_SplayDynOpt_Supplement_splitCost
-- name    : SplayDynOpt_Supplement_splitCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:08:58.32565+00:00
-- url     : https://prove2.me/theorems/55e80712-35c7-42af-9d5c-8dfaa67af912
-- title:
--   The cost of the splitting process of a splay tree
-- statement:
--   Let $T$ be a binary search tree and $\sigma=x_1,\dots,x_m$ a sequence of keys. The **splitting process** performs $\mathrm{split}(x_1),\dots,\mathrm{split}(x_m)$ starting from $T$. A split at $x$ in the current tree containing $x$ first splays $x$ to the root (bottom-up splaying), and then deletes $x$; the left and right subtrees of $x$ become two independent binary search trees, on the keys below $x$ and above $x$. Each later key is split inside the unique current tree that still contains it.
--
--   The cost of a split is the BST-model cost of its splay, $1$ plus the number of rotations; the root deletion is free. Writing $\mathrm{splay}(x,T)=x(L,R)$ with cost $c$, the total cost $\mathrm{splitCost}(T,\sigma)$ satisfies
--   $$
--   \mathrm{splitCost}(T,x::\sigma)=c+\mathrm{splitCost}\big(L,\sigma_{<x}\big)+\mathrm{splitCost}\big(R,\sigma_{>x}\big),\qquad \mathrm{splitCost}(T,[\,])=0,
--   $$
--   where $\sigma_{<x}$ and $\sigma_{>x}$ are the subsequences of $\sigma$ of keys below and above $x$, in order.
--
--   This is the quantity bounded in Theorem 48; the split conjecture asks whether it is $O(n)$ for every initial tree on $[n]$ and every order of the $n$ splits.
--
--   **Formalization Note** The forest of current trees is represented by the recursion: the later splits inside $L$ are exactly the later keys below $x$, because $L$ holds exactly those keys. Splaying and its cost are the published `SplayDynOpt.splay` and `SplayDynOpt.accessCost`. On inputs outside the process (a key absent from its tree) the value carries no meaning; Theorem 48 applies the function only to a binary search tree on $[n]$ and a permutation of $[n]$.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), App. D, p.77 (the split operation) and p.78 (split conjecture; root deletes are free)

import Mathlib
import Definitions.Def_SplayDynOpt_splayCost

set_option autoImplicit false

namespace SplayDynOpt.Supplement

open BinaryTree SplayDynOpt

/-- **The cost of the splitting process of a splay tree.** `splitCost T σ` is the total cost of the
operations `split(x₁), …, split(x_m)` for `σ = x₁, …, x_m`, starting from the tree `T`: the split
at `x₁` splays `x₁` to the root of `T` (bottom-up, the published `SplayDynOpt.splay`), paying
`accessCost = 1 + #rotations`, then deletes the root `x₁` for free; its left subtree `L` and right
subtree `R` become two independent trees, and every later key is split inside the unique current
tree that contains it. Since `L` holds exactly the keys below `x₁` and `R` the keys above, the
later splits inside `L` are the later keys `< x₁`, in their order, and similarly for `R`.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), App. D, p.77:
"A split at x first rebuilds the tree so that x becomes the root and then deletes x. After the
deletion, the left and right subtrees of x become two independent BSTs on the key sets
{y ∈ S : y < x} and {y ∈ S : y > x}. If we continue performing splits, each subsequent key is split
inside the unique current tree that still contains it. For splay trees, we restructure the tree
simply by splaying x."; p.78: "accounting for the deletion of the root requires only free
operations".

**Formalization Note.** The forest of current trees is represented recursively: after the split
at `x`, the rest of the sequence is routed to `L` (keys `< x`) and `R` (keys `> x`), which is the
same process as the forest process because the two trees evolve independently. The cost of a
split is the BST-model cost `1 + #rotations` of the splay (§2.1, p.3); the root deletion is free.
On inputs outside the process (a key not in the current tree, so the splay leaves the tree
unchanged) the value is junk; Theorem 48 only applies it to a BST on `[n]` and a permutation of
`[n]`, where every key is present when it is split. -/
def splitCost : BinaryTree ℕ → List ℕ → ℕ
  | _, [] => 0
  | T, x :: σ =>
      match (splay x T).1 with
      | node _ L R =>
          accessCost (splay x T).2 + splitCost L (σ.filter (· < x)) +
            splitCost R (σ.filter (x < ·))
      | nil => accessCost (splay x T).2
termination_by _ σ => σ.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_unattach]
    exact Nat.lt_succ_of_le ((List.length_filter_le _ _).trans (le_of_eq List.length_attach))

end SplayDynOpt.Supplement


