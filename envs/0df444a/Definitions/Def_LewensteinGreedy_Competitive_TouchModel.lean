-- Prove2me | Definitions.Def_LewensteinGreedy_Competitive_TouchModel
-- name    : LewensteinGreedy_Competitive_TouchModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:31:16.32429+00:00
-- url     : https://prove2.me/theorems/016578b2-51b0-4d33-be8d-81cf1844cf30
-- title:
--   The node-touch BST model and the free-initialization optimum $\mathrm{OPT}_n(X)$ (§1.2, §2.1.1)
-- statement:
--   The key universe is $[n]=\{1,\dots,n\}$ and an access sequence is a finite list $X=(x_1,\dots,x_m)$ of keys of $[n]$ (repetitions allowed, $m=0$ allowed). A BST on $[n]$ is the published `SplayDynOpt.IsBSTOn n`.
--
--   **Cost model (§2.1.1).** Serving request $x_t$ from the current BST $T$ touches a set $S_t$ of keys that forms a connected subtree of $T$ containing both the root and $x_t$. These nodes may be rearranged into any BST on the same keys; every subtree outside $S_t$ keeps its internal structure and is reattached in the position required by key order. The access costs $|S_t|$, and an execution costs $\sum_{t=1}^m |S_t|$.
--
--   **$\mathrm{OPT}_n(X)$** is the minimum cost of an offline execution serving $X$, with its initial BST on $[n]$ chosen freely (independently of any tree given to Greedy).
--
--   **Formalization Note.** `RootClosed S T`: an unselected node of $T$ has no selected key in its subtree (so, with $x\in S$, $S$ is a root-containing connected subtree). `fringe S T` lists the outside subtrees of $T$ in inorder, including empty slots. `TouchStep n x T T' S`: $T,T'$ are BSTs on $[n]$, $S\subseteq[n]$, $x\in S$, $S$ is root-closed in both trees and `fringe S T = fringe S T'` (outside subtrees unchanged and in the same inorder slots). A `TouchExecution` lists the trees (`trees 0` is the freely chosen initial tree) and touch sets; `serves n X` requires a legal step for every request; `OPT n X` is the natural-number infimum of the costs, a minimum since the feasible set is nonempty for every valid $X$ (walk the search path and rearrange nothing). The value $0$ of the infimum of an empty set occurs only for an invalid $X$, which no statement uses.
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, §1.2 and §2.1.1, printed p. 2, 4 / PDF 3, 5

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn

set_option autoImplicit false

namespace LewensteinGreedy.Competitive

open BinaryTree SplayDynOpt

/-!
# The node-touch BST model and the free-initialization optimum `OPT_n(X)`

Lewenstein, *Greedy BST is O(log log n)-Competitive*, supplied 2026 artifact (SHA-256
04ac49f6…), §1.2, printed p.2 / PDF 3, and §2.1.1, printed p.4 / PDF 5.

* Keys are the natural numbers `1, …, n`; a BST on `[n]` is `SplayDynOpt.IsBSTOn n`.
* `ValidSequence n X`: every request of the finite access sequence `X` lies in `[n]`
  (repetitions allowed, `X` may be empty).
* `RootClosed S T`: the keys of `S` that occur in `T` form a subtree of `T` containing the root
  (an unselected node has no selected descendant). With `x ∈ S` this is the source's
  "connected subtree of the current BST containing both the root and `x_t`".
* `fringe S T`: the subtrees hanging off the selected part, listed in inorder, including the
  empty attachment slots.
* `TouchStep n x T T' S`: serving request `x` from `T` touches exactly `S` and leaves `T'`:
  `S` is root-closed in `T` and contains `x`; `T'` is a BST on the same keys in which `S` is again
  root-closed; and every outside subtree keeps its internal structure and is reattached in the
  inorder slot required by key order (`fringe S T = fringe S T'`). The cost of the step is `|S|`.
* `TouchExecution`: an offline execution, i.e. an initial tree `trees 0` (chosen freely) and for
  each request `t` a touch set `touches t` and resulting tree `trees (t+1)`.
* `OPT n X`: the minimum of `∑_t |S_t|` over all executions serving `X` from any initial BST on
  `[n]`. The feasible set is nonempty for every valid `X` (search along the root-to-key path,
  rearrange nothing); `sInf ∅ = 0` occurs only for an invalid `X`, which no statement uses.
-/

/-- Every request lies in `[n] = {1, …, n}`. -/
def ValidSequence (n : ℕ) (X : List ℕ) : Prop := ∀ x ∈ X, x ∈ Finset.Icc 1 n

/-- Root-closed selection: a selected node's subtrees are again root-closed; an unselected node
has no selected key in its subtree. -/
def RootClosed (S : Finset ℕ) : BinaryTree ℕ → Prop
  | nil => True
  | node a l r =>
    if a ∈ S then RootClosed S l ∧ RootClosed S r
    else Disjoint S (keys (node a l r))

/-- The outside subtrees of a root-closed selection, in inorder, including empty slots. -/
def fringe (S : Finset ℕ) : BinaryTree ℕ → List (BinaryTree ℕ)
  | nil => [nil]
  | node a l r => if a ∈ S then fringe S l ++ fringe S r else [node a l r]

/-- One legal access to `x` in the node-touch model: touch the connected root-containing set `S`
(which contains `x`), rearrange it into any BST on the same keys, and reattach the untouched
subtrees unchanged in key order. -/
def TouchStep (n x : ℕ) (T T' : BinaryTree ℕ) (S : Finset ℕ) : Prop :=
  IsBSTOn n T ∧ IsBSTOn n T' ∧ S ⊆ Finset.Icc 1 n ∧ x ∈ S ∧
  RootClosed S T ∧ RootClosed S T' ∧ fringe S T = fringe S T'

/-- An offline BST execution: trees before/after each access and the touch set of each access.
The initial tree `trees 0` is part of the execution (free initialization). -/
structure TouchExecution where
  trees : ℕ → BinaryTree ℕ
  touches : ℕ → Finset ℕ

/-- The execution serves `X` on `[n]`: its initial tree is a BST on `[n]` and the `j`-th access
(0-based) is a legal touch step for the request `X[j]`. -/
def TouchExecution.serves (e : TouchExecution) (n : ℕ) (X : List ℕ) : Prop :=
  IsBSTOn n (e.trees 0) ∧ ∀ j : Fin X.length,
    TouchStep n X[j] (e.trees j.val) (e.trees (j.val + 1)) (e.touches j.val)

/-- Total node-touch cost `∑_{t=1}^{m} |S_t|` of the first `m` accesses. -/
def TouchExecution.cost (e : TouchExecution) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, (e.touches j).card

/-- `OPT_n(X)`: the minimum node-touch cost of an offline BST execution serving `X`, with its
initial BST on `[n]` chosen freely (§1.2, §2.1.1). -/
noncomputable def OPT (n : ℕ) (X : List ℕ) : ℕ :=
  sInf {c | ∃ e : TouchExecution, e.serves n X ∧ e.cost X.length = c}

end LewensteinGreedy.Competitive


