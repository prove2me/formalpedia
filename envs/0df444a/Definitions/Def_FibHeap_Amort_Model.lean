-- Prove2me | Definitions.Def_FibHeap_Amort_Model
-- name    : FibHeap_Amort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:02:12.365673+00:00
-- url     : https://prove2.me/theorems/75852ab9-2dca-4a2a-b202-e4bf803c8a8d
-- title:
--   §§1–2, pp. 597–604 — F-heap trees and linking, the heap operations with linking steps and cascading cuts, unit costs, runs, the potential
-- statement:
--   This file fixes the Fibonacci heap (F-heap) of Fredman and Tarjan as a state machine, together with the paper's unit cost accounting.
--
--   **Trees.** An F-heap tree is a heap-ordered rooted tree: every child's key is at least its parent's key. Each node stores an item (a natural number used as an identifier), the item's real key, and a mark bit. The children of a node are listed in the order in which they were linked to it, earliest first. The **rank** $r(x)$ of a node $x$ is its number of children, and the **size** of $x$ is its number of descendants, $x$ itself included. The bare tree type can also express arbitrary trees; runs from no heaps produce the F-heaps used in the theorems.
--
--   **Linking** (p. 598). Given two trees with roots $x$ and $y$: if the key of $x$ is smaller than the key of $y$, then $y$ becomes the last child of $x$; otherwise $x$ becomes the last child of $y$. The root that becomes a child is unmarked (p. 603).
--
--   **Heaps and collections.** A heap is its list of roots; a collection of heaps is a list of heaps, and heaps are named by their positions in that list. Initially there are no heaps. The number of items of a heap $h$ is written $n(h)$.
--
--   **The linking loop** (p. 599). Starting from a list of roots, repeat the *linking step* "find any two trees whose roots have the same rank, and link them" until no two roots have the same rank. Every order of linking is allowed; the relation records the final root list and the number $L$ of linking steps.
--
--   **Cuts and cascading cuts** (pp. 601–603). Cutting a nonroot node $x$ from its parent $p(x)$ makes the subtree of $x$ a new tree of the heap (for *delete*, $x$ is destroyed and its children become roots instead). After the cut, if $p(x)$ is not a root, it is marked if it was unmarked, and it is itself cut from its parent if it was marked (a **cascading cut**), which may repeat further up. A root is never marked by a cut.
--
--   **Operations** (§1, p. 597, and §2). *make heap* adds an empty heap. *find min* $(h)$ requires a nonempty heap and leaves the collection unchanged. *insert* $(i, h)$ with key $k$ adds a one-node tree for a new item $i$ (an item in no heap) to the roots of $h$. *meld* $(h_1, h_2)$, for $h_1 \neq h_2$, puts the union of the two root lists in $h_1$ and leaves $h_2$ empty. *delete min* $(h)$, for a nonempty heap, removes a root $x$ of minimum key, adds the children of $x$ to the roots, and runs the linking loop. *decrease key* $(\Delta, i, h)$, for $\Delta \ge 0$, subtracts $\Delta$ from the key of $i$; if $i$ is not in a root, its node is cut (with cascading cuts). *delete* $(i, h)$: if $i$ is in a root of minimum key, it proceeds as delete min; if it is in another root, that root is removed and its children join the roots; otherwise its node is cut (with cascading cuts) and destroyed, and its children join the roots.
--
--   **Cost.** The actual time of an operation is
--
--   $$\mathrm{cost} = 1 + L + (\text{number of cuts}) + \mathrm{scan},$$
--
--   one unit for the operation, one per linking step (p. 601), one per cut, first or cascading (p. 604), and, for delete min (and delete of a minimum root), the scan of the rank array, which is the maximum rank of the deleted node and of the roots after linking (p. 600: "proportional to the maximum rank of any of the nodes manipulated plus the number of linking steps").
--
--   **Potential** (p. 604). The potential $\Phi$ of a collection is the number of trees plus twice the number of marked nonroot nodes, summed over all heaps. The **amortized time** of an operation is its cost plus the increase in potential it causes (p. 600).
--
--   **Runs.** A run of $T$ operations starts from no heaps and performs $T$ steps; a collection is **reachable** if some run produces it. The budget of THEOREM 1 is $C\,(\log_2 n(h) + 1)$ for a delete min or delete on heap $h$ (with $n(h)$ read before the operation) and $C$ for every other operation.
--
--   These objects support the amortized analysis of §2 (Lemma 1, Corollary 1 and Theorem 1).
--
--   **Formalization Note** The minimum-node pointer and returned items are not stored: find min is represented by a state-preserving step, and costs are charged as if the pointer were maintained, as the paper's $O(1)$ find min presupposes. Delete min may choose any minimum-key root, while the tie rule inside `link` is fixed. The order of linking steps is arbitrary. A melded-away heap stays as an empty heap at its index. The step relation fixes the step data (linking steps, cuts, cascading cuts, scan), so the cost cannot be chosen freely.
-- source:
--   Fredman and Tarjan, Fibonacci heaps and their uses in improved network optimization algorithms, J. ACM 34 (1987), pp. 597–604, §1 and §2

import Mathlib

namespace FibHeap.Amort

/-- A node of an F-heap tree: its item (an identifier), the item's real key, its mark bit, and its
children, listed in the order they were linked to it, earliest first. -/
inductive FTree where
  | node (item : ℕ) (key : ℝ) (marked : Bool) (children : List FTree)

namespace FTree

/-- The item stored in the root of the tree. -/
def item : FTree → ℕ
  | node i _ _ _ => i

/-- The key of the item stored in the root of the tree. -/
def key : FTree → ℝ
  | node _ k _ _ => k

/-- The mark bit of the root of the tree. -/
def marked : FTree → Bool
  | node _ _ m _ => m

/-- The children of the root, in linking order (earliest first). -/
def children : FTree → List FTree
  | node _ _ _ cs => cs

/-- The rank `r(x)`: the number of children of the root. -/
def rank (t : FTree) : ℕ := t.children.length

/-- The same tree with the root's mark bit set to `b`. -/
def setMarked (b : Bool) : FTree → FTree
  | node i k _ cs => node i k b cs

/-- The same tree with the root's key replaced by `k'`. -/
def setKey (k' : ℝ) : FTree → FTree
  | node i _ m cs => node i k' m cs

/-- The number of descendants of the root, including itself. -/
def size : FTree → ℕ
  | node _ _ _ cs => 1 + (cs.map size).sum

/-- All subtrees: the tree itself, then the subtrees of every child. These are the nodes. -/
def subtrees : FTree → List FTree
  | node i k m cs => node i k m cs :: cs.flatMap subtrees

/-- The items of all nodes of the tree. -/
def items (t : FTree) : List ℕ := t.subtrees.map item

/-- The number of marked nodes of the tree (the root included). -/
def markedCount : FTree → ℕ
  | node _ _ m cs => (if m then 1 else 0) + (cs.map markedCount).sum

end FTree

open FTree

/-- Linking (p. 598): if the item in `x` has the smaller key, `y` becomes the last child of `x`;
otherwise `x` becomes the last child of `y`. The new child is unmarked (p. 603). -/
noncomputable def link (x y : FTree) : FTree :=
  if x.key < y.key then
    .node x.item x.key x.marked (x.children ++ [y.setMarked false])
  else
    .node y.item y.key y.marked (y.children ++ [x.setMarked false])

/-- A heap is its list of roots. -/
abbrev Heap := List FTree

/-- A collection of heaps; heap names are list indices. -/
abbrev Coll := List Heap

/-- The number of items in a heap. -/
def heapSize (r : Heap) : ℕ := (r.map size).sum

/-- The items of a heap. -/
def heapItems (r : Heap) : List ℕ := r.flatMap items

/-- The number of marked nonroot nodes of a heap. -/
def markedNonroot (r : Heap) : ℕ := (r.map fun τ => (τ.children.map markedCount).sum).sum

/-- The potential (p. 604): the number of trees plus twice the number of marked nonroot nodes,
summed over all heaps of the collection. -/
def potential (s : Coll) : ℕ := (s.map fun r => r.length + 2 * markedNonroot r).sum

/-- The maximum rank of the roots of a heap (`0` for the empty heap). -/
def maxRank (r : Heap) : ℕ := (r.map rank).foldr max 0

/-- The linking loop of delete min (p. 599): `Consolidate rs rs' n` says that repeating the linking
step "find any two trees whose roots have the same rank, and link them" on the root list `rs`, in
some order, until no two roots have the same rank, ends with the root list `rs'` after `n` linking
steps. -/
inductive Consolidate : Heap → Heap → ℕ → Prop
  | done {rs : Heap} : (rs.map rank).Nodup → Consolidate rs rs 0
  | step {rs rest rs' : Heap} {a b : FTree} {n : ℕ} :
      rs.Perm (a :: b :: rest) → a.rank = b.rank →
      Consolidate (link a b :: rest) rs' n → Consolidate rs rs' (n + 1)

/-- Cutting with cascading cuts (pp. 601–603). `CutAt i f t t' R n lost` walks the tree `t` down
to the child node containing item `i`, cuts it from its parent and puts `f` of it among the new
roots. Going back up, a node that lost a child is marked if it was unmarked, and is itself cut
(a cascading cut) if it was marked. The result is the remaining tree `t'`, the list `R` of new
roots, the number `n` of cascading cuts, and whether the root of `t` lost a child (`lost`), which
the caller uses only when the root of `t` is not a root of the heap. -/
inductive CutAt (i : ℕ) (f : FTree → List FTree) : FTree → FTree → List FTree → ℕ → Bool → Prop
  | direct {it : ℕ} {k : ℝ} {m : Bool} {pre post : List FTree} {c : FTree} :
      c.item = i →
      CutAt i f (.node it k m (pre ++ c :: post)) (.node it k m (pre ++ post)) (f c) 0 true
  | markParent {it : ℕ} {k : ℝ} {m : Bool} {pre post : List FTree} {c c' : FTree}
      {R : List FTree} {n : ℕ} :
      CutAt i f c c' R n true → c.marked = false →
      CutAt i f (.node it k m (pre ++ c :: post)) (.node it k m (pre ++ c'.setMarked true :: post))
        R n false
  | cascade {it : ℕ} {k : ℝ} {m : Bool} {pre post : List FTree} {c c' : FTree}
      {R : List FTree} {n : ℕ} :
      CutAt i f c c' R n true → c.marked = true →
      CutAt i f (.node it k m (pre ++ c :: post)) (.node it k m (pre ++ post)) (R ++ [c'])
        (n + 1) true
  | pass {it : ℕ} {k : ℝ} {m : Bool} {pre post : List FTree} {c c' : FTree}
      {R : List FTree} {n : ℕ} :
      CutAt i f c c' R n false →
      CutAt i f (.node it k m (pre ++ c :: post)) (.node it k m (pre ++ c' :: post)) R n false

/-- The step data of an operation: linking steps, cuts (first and cascading), cascading cuts,
and the rank scan of delete min. -/
structure StepData where
  links : ℕ
  cuts : ℕ
  cascading : ℕ
  scan : ℕ

/-- The step data of an operation with no linking step, no cut and no scan. -/
def StepData.zero : StepData := ⟨0, 0, 0, 0⟩

/-- The actual time of an operation in the paper's unit accounting: one unit for the operation,
one per linking step, one per cut, plus the rank scan of delete min. -/
def cost (d : StepData) : ℕ := 1 + d.links + d.cuts + d.scan

/-- The F-heap operations of §1, p. 597. -/
inductive Op where
  | makeHeap
  | findMin (h : ℕ)
  | insert (i : ℕ) (k : ℝ) (h : ℕ)
  | meld (h₁ h₂ : ℕ)
  | deleteMin (h : ℕ)
  | decreaseKey (Δ : ℝ) (i h : ℕ)
  | delete (i h : ℕ)

/-- One F-heap operation (§2, pp. 599–603): `Step s op s' d` says that performing `op` on the
collection `s` may yield the collection `s'` with step data `d`. A step exists only when the
operation's precondition holds. -/
inductive Step : Coll → Op → Coll → StepData → Prop
  | makeHeap {s : Coll} : Step s .makeHeap (s ++ [[]]) StepData.zero
  | findMin {s : Coll} {h : ℕ} {r : Heap} :
      s[h]? = some r → r ≠ [] → Step s (.findMin h) s StepData.zero
  | insert {s : Coll} {r : Heap} {i : ℕ} {k : ℝ} {h : ℕ} :
      s[h]? = some r → (∀ r' ∈ s, i ∉ heapItems r') →
      Step s (.insert i k h) (s.set h (r ++ [.node i k false []])) StepData.zero
  | meld {s : Coll} {r₁ r₂ : Heap} {h₁ h₂ : ℕ} :
      s[h₁]? = some r₁ → s[h₂]? = some r₂ → h₁ ≠ h₂ →
      Step s (.meld h₁ h₂) ((s.set h₁ (r₁ ++ r₂)).set h₂ []) StepData.zero
  | deleteMin {s : Coll} {h : ℕ} {pre post r' : Heap} {x : FTree} {L : ℕ} :
      s[h]? = some (pre ++ x :: post) →
      (∀ y ∈ pre ++ x :: post, x.key ≤ y.key) →
      Consolidate (pre ++ post ++ x.children) r' L →
      Step s (.deleteMin h) (s.set h r') ⟨L, 0, 0, max x.rank (maxRank r')⟩
  | decreaseKeyRoot {s : Coll} {h : ℕ} {pre post : Heap} {x : FTree} {Δ : ℝ} {i : ℕ} :
      0 ≤ Δ → s[h]? = some (pre ++ x :: post) → x.item = i →
      Step s (.decreaseKey Δ i h) (s.set h (pre ++ x.setKey (x.key - Δ) :: post)) StepData.zero
  | decreaseKeyCut {s : Coll} {h : ℕ} {pre post : Heap} {τ τ' : FTree} {R : List FTree}
      {n : ℕ} {lost : Bool} {Δ : ℝ} {i : ℕ} :
      0 ≤ Δ → s[h]? = some (pre ++ τ :: post) → τ.item ≠ i →
      CutAt i (fun c => [c.setKey (c.key - Δ)]) τ τ' R n lost →
      Step s (.decreaseKey Δ i h) (s.set h (pre ++ τ' :: post ++ R)) ⟨0, 1 + n, n, 0⟩
  | deleteMinRoot {s : Coll} {h : ℕ} {pre post r' : Heap} {x : FTree} {L : ℕ} {i : ℕ} :
      s[h]? = some (pre ++ x :: post) → x.item = i →
      (∀ y ∈ pre ++ x :: post, x.key ≤ y.key) →
      Consolidate (pre ++ post ++ x.children) r' L →
      Step s (.delete i h) (s.set h r') ⟨L, 0, 0, max x.rank (maxRank r')⟩
  | deleteOtherRoot {s : Coll} {h : ℕ} {pre post : Heap} {x : FTree} {i : ℕ} :
      s[h]? = some (pre ++ x :: post) → x.item = i →
      (∃ y ∈ pre ++ post, y.key ≤ x.key) →
      Step s (.delete i h) (s.set h (pre ++ post ++ x.children)) StepData.zero
  | deleteCut {s : Coll} {h : ℕ} {pre post : Heap} {τ τ' : FTree} {R : List FTree}
      {n : ℕ} {lost : Bool} {i : ℕ} :
      s[h]? = some (pre ++ τ :: post) → τ.item ≠ i →
      CutAt i (fun c => c.children) τ τ' R n lost →
      Step s (.delete i h) (s.set h (pre ++ τ' :: post ++ R)) ⟨0, 1 + n, n, 0⟩

/-- The preconditions of the operations (§1, p. 597): the heaps named exist, an inserted item is
in no heap, melded heaps are distinct, find min and delete min act on nonempty heaps, decrease key subtracts
a nonnegative amount, and decrease key and delete act on an item of the heap. -/
def Valid (s : Coll) : Op → Prop
  | .makeHeap => True
  | .findMin h => ∃ r, s[h]? = some r ∧ r ≠ []
  | .insert i _ h => h < s.length ∧ ∀ r ∈ s, i ∉ heapItems r
  | .meld h₁ h₂ => h₁ < s.length ∧ h₂ < s.length ∧ h₁ ≠ h₂
  | .deleteMin h => ∃ r, s[h]? = some r ∧ r ≠ []
  | .decreaseKey Δ i h => 0 ≤ Δ ∧ ∃ r, s[h]? = some r ∧ i ∈ heapItems r
  | .delete i h => ∃ r, s[h]? = some r ∧ i ∈ heapItems r

/-- A run of `T` operations starting from no heaps: states `s 0 = [], s 1, …, s T`, and, for each
`t < T`, the operation `op t` with step data `d t` taking `s t` to `s (t + 1)`. -/
def IsRun (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData) : Prop :=
  s 0 = [] ∧ ∀ t < T, Step (s t) (op t) (s (t + 1)) (d t)

/-- A collection of heaps is reachable if some run from no heaps produces it. -/
def Reachable (c : Coll) : Prop :=
  ∃ (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData), IsRun T s op d ∧ s T = c

/-- The per-operation budget in THEOREM 1: `C (log₂ n + 1)` for delete min and delete, where `n`
is the number of items in the heap operated on, and `C` for every other operation. -/
noncomputable def opBound (C : ℝ) (s : Coll) : Op → ℝ
  | .deleteMin h => C * (Real.logb 2 (heapSize (s.getD h [])) + 1)
  | .delete _ h => C * (Real.logb 2 (heapSize (s.getD h [])) + 1)
  | _ => C

/-- The amortized time (p. 600): the actual time plus the net increase in potential. -/
def amortized (d : StepData) (s s' : Coll) : ℤ :=
  (cost d : ℤ) + (potential s' : ℤ) - (potential s : ℤ)

end FibHeap.Amort


