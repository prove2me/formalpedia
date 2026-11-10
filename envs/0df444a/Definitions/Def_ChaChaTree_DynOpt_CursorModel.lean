-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_CursorModel
-- name    : ChaChaTree_DynOpt_CursorModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:10.890581+00:00
-- url     : https://prove2.me/theorems/1f511c68-63a8-4206-beed-f9fe55829843
-- title:
--   The BST model of §5.1 (cursor model), offline OPT, and deterministic online BST algorithms
-- statement:
--   **The BST model** (§5.1). There is a static universe of keys $[n] = \{1,\dots,n\}$, an access sequence $X = (x_1,\dots,x_m)$, and a binary search tree in which every node has a unique key from $[n]$ (`SplayDynOpt.IsBSTOn n t`), initially chosen arbitrarily. To serve the $t$-th access $x_t$, a **cursor** is placed at the root, and the algorithm performs a sequence of unit-cost actions:
--
--   * move the cursor to the parent, the left child or the right child of its node (illegal if that node does not exist);
--   * rotate the cursor's node with its parent (`SplayDynOpt.rotateAt`; illegal at the root); the cursor stays on its node;
--   * **finish** the access, allowed only if the cursor has, at some point during this access, been on the node with key $x_t$; it is the last action of the access.
--
--   Changes to the tree persist. `serveAccess x t as` is the tree after a valid service of access $x$ from tree $t$ with action list `as`, or `none`; `execute X t₀ plan` chains the accesses. The cost of an execution, `planCost`, is the total number of actions (finish included).
--
--   **OPT.** `IsValidExecution n X t₀ plan`: $t_0$ is a BST on exactly $[n]$ and every access is validly served. $\mathrm{OPT}(n, X)$ is the minimum cost over all valid (offline) executions, with a free choice of initial tree and of every action: the infimum of a set of naturals, nonempty whenever every $x_t \in [n]$ (walk down by binary search and finish).
--
--   **Online algorithms.** `OnlineBSTAlg n` is a deterministic online algorithm: an initial tree `init`, fixed independently of $X$, and a rule `plan` giving the action list of access $t$ as a function of the prefix $(x_1,\dots,x_t)$ only, so it cannot depend on later accesses or on $m$. `A.Serves X`: the initial tree is a BST on $[n]$ and every produced list is a valid service. `A.cost X` is the total number of actions it performs on $X$.
--
--   **Formalization Note.** Since keys are distinct, the cursor's node is identified with its key, and moves are located by binary search (`subtreeAt`, `leftChildKey`, `rightChildKey`, `parentKey`). The leaf-oriented and pointer-machine models of §5.1 are proof devices of the paper and are not defined here.
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §5.1, p. 21 (PDF 22); §1.1, p. 2 (PDF 3)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_rotateAt

set_option autoImplicit false

namespace ChaChaTree.DynOpt

open BinaryTree

/-! # The BST model of §5.1 (cursor model), its executions, `OPT`, and online algorithms

Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, *Dynamic Optimality to within
O(log log log n)*, STOC 2027 submission (manuscript, sha256 9316fbfd…), §5.1, p. 21 (PDF 22).

Trees are `BinaryTree ℕ`; a tree on the keys `[n]` is `SplayDynOpt.IsBSTOn n t`. Since keys are
distinct, the node the cursor is on is identified with its key. -/

/-- The subtree rooted at the node with key `c`, found by binary search (`nil` if absent). -/
def subtreeAt (c : ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | nil => nil
  | node a l r => if c = a then node a l r else if c < a then subtreeAt c l else subtreeAt c r

/-- The key of the left child of the node with key `c` (`none` if there is none). -/
def leftChildKey (c : ℕ) (t : BinaryTree ℕ) : Option ℕ :=
  match subtreeAt c t with
  | nil => none
  | node _ l _ => SplayDynOpt.root l

/-- The key of the right child of the node with key `c` (`none` if there is none). -/
def rightChildKey (c : ℕ) (t : BinaryTree ℕ) : Option ℕ :=
  match subtreeAt c t with
  | nil => none
  | node _ _ r => SplayDynOpt.root r

/-- The key of the parent of the node with key `c` (`none` at the root or if `c` is absent). -/
def parentKey (c : ℕ) : BinaryTree ℕ → Option ℕ
  | nil => none
  | node a l r =>
      if c = a then none
      else if c < a then (if SplayDynOpt.root l = some c then some a else parentKey c l)
      else (if SplayDynOpt.root r = some c then some a else parentKey c r)

/-- The unit-cost actions of the BST model (§5.1): move the cursor to the parent, left child or
right child; rotate the cursor's node with its parent; finish the access. -/
inductive Action
  | moveParent
  | moveLeft
  | moveRight
  | rotate
  | finish
  deriving DecidableEq, Repr

/-- One non-finishing action applied to the configuration `(tree, cursor key)`: `none` when the
action is illegal (the target node does not exist; rotation at the root). A rotation acts on the
node the cursor is on and its parent (`SplayDynOpt.rotateAt`); the cursor stays on its node.
`finish` is not a step and is handled by `runAccess`. -/
def step (t : BinaryTree ℕ) (c : ℕ) : Action → Option (BinaryTree ℕ × ℕ)
  | .moveParent => (parentKey c t).map fun p => (t, p)
  | .moveLeft => (leftChildKey c t).map fun l => (t, l)
  | .moveRight => (rightChildKey c t).map fun r => (t, r)
  | .rotate => if (parentKey c t).isSome then some (SplayDynOpt.rotateAt c t, c) else none
  | .finish => none

/-- Serving one access to key `x` with the action list `as`, from tree `t`, cursor on key `c`,
`v` recording whether the cursor has already been on the node with key `x` during this access.
The result is the tree after the access, or `none` if the list is not a valid service:
every action must be legal, the list must end with `finish` and contain no other `finish`, and
`finish` is allowed only if the cursor has been on `x` at some point during the access. -/
def runAccess (x : ℕ) : BinaryTree ℕ → ℕ → Bool → List Action → Option (BinaryTree ℕ)
  | _, _, _, [] => none
  | t, _, v, [.finish] => if v then some t else none
  | _, _, _, .finish :: _ :: _ => none
  | t, c, v, a :: as =>
      match step t c a with
      | none => none
      | some (t', c') => runAccess x t' c' (v || decide (c' = x)) as

/-- Serving access `x` from tree `t` with the action list `as`: the cursor is placed at the root
(§5.1: "To serve the tth access (to the key xt), a cursor is placed at the root of the tree"). -/
def serveAccess (x : ℕ) (t : BinaryTree ℕ) (as : List Action) : Option (BinaryTree ℕ) :=
  match SplayDynOpt.root t with
  | none => none
  | some r => runAccess x t r (decide (r = x)) as

/-- Executing the access sequence `X` from the tree `t` with one action list per access; changes
to the tree persist. `none` if some access is not validly served or the number of action lists
differs from `|X|`; otherwise the final tree. -/
def execute : List ℕ → BinaryTree ℕ → List (List Action) → Option (BinaryTree ℕ)
  | [], t, [] => some t
  | x :: X, t, as :: plan => (serveAccess x t as).bind fun t' => execute X t' plan
  | _, _, _ => none

/-- An (offline) **valid execution** of `X` in the BST model on keys `[n]`: an initial binary
search tree on exactly the keys `[n]`, chosen freely, and one valid action list per access. -/
def IsValidExecution (n : ℕ) (X : List ℕ) (t₀ : BinaryTree ℕ) (plan : List (List Action)) :
    Prop :=
  SplayDynOpt.IsBSTOn n t₀ ∧ (execute X t₀ plan).isSome

/-- The cost of an execution: the total number of actions over all accesses (each unit cost,
`finish` included). -/
def planCost (plan : List (List Action)) : ℕ :=
  (plan.map List.length).sum

/-- **`OPT(X)`** on keys `[n]`: the minimum cost of any valid (offline) execution of `X` in the
BST model of §5.1, over every initial tree and every choice of actions (pp. 2, 21).

The set is nonempty whenever every access is in `[n]` (search down from the root and finish);
`sInf ∅ = 0` only for an `X` with a key outside `[n]`, which no statement uses. -/
noncomputable def OPT (n : ℕ) (X : List ℕ) : ℕ :=
  sInf {c : ℕ | ∃ t₀ plan, IsValidExecution n X t₀ plan ∧ planCost plan = c}

/-- A **deterministic online BST algorithm** on keys `[n]`: an initial tree, fixed before the
sequence is seen, and a rule giving the action list for access `t` as a function of the prefix
`(x₁, …, x_t)` alone (§5.1). It cannot see later accesses or the length `m`; being a function,
it is deterministic. -/
structure OnlineBSTAlg (n : ℕ) where
  /-- The initial tree, independent of the access sequence. -/
  init : BinaryTree ℕ
  /-- `plan (x₁, …, x_t)` is the action list the algorithm performs for the access `x_t`. -/
  plan : List ℕ → List Action

/-- The action lists `A` produces on `X`: for access `t`, `A.plan (x₁, …, x_t)`. -/
def OnlineBSTAlg.plans {n : ℕ} (A : OnlineBSTAlg n) (X : List ℕ) : List (List Action) :=
  (List.range X.length).map fun t => A.plan (X.take (t + 1))

/-- `A` **serves** `X`: its initial tree is a BST on `[n]` and every action list it produces is
a valid service of its access. -/
def OnlineBSTAlg.Serves {n : ℕ} (A : OnlineBSTAlg n) (X : List ℕ) : Prop :=
  IsValidExecution n X A.init (A.plans X)

/-- The cost of `A` on `X`: the total number of actions it performs. -/
def OnlineBSTAlg.cost {n : ℕ} (A : OnlineBSTAlg n) (X : List ℕ) : ℕ :=
  planCost (A.plans X)

end ChaChaTree.DynOpt


