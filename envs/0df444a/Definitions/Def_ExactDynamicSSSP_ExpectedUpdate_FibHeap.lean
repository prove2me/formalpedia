-- Prove2me | Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_FibHeap
-- name    : ExactDynamicSSSP_ExpectedUpdate_FibHeap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:22:51.15325+00:00
-- url     : https://prove2.me/theorems/8ecb0a84-9d18-4764-a65b-dd7d5815e698
-- title:
--   §5, App. B.1 — an indexed Fibonacci heap with instrumented actual work
-- statement:
--   The global propagation container $C_{\rm main}$ is a Fibonacci heap (Fredman–Tarjan 1987). This file gives a concrete indexed Fibonacci heap whose handles are the vertices and whose keys lie in $[0,\infty]$, with the standard operations:
--
--   1. **insert** adds a singleton tree to the root list and compares it with the minimum;
--   2. **decrease-key** lowers a key; if heap order with the parent is violated the node is cut to the root list and a cascading cut follows (a marked non-root is cut and the cascade continues at its parent; an unmarked non-root is marked);
--   3. **delete-min** removes the minimum root, moves its children to the root list, links roots of equal degree through a degree table (the larger key becomes the child), and rebuilds the root list and the minimum by scanning the table.
--
--   Every operation returns, besides the new heap, its **actual work**: one unit per root insertion, key comparison, cut, link, root scanned, child moved and table slot scanned. No amortized bound is built into these counts; amortization is a theorem about them.
--
--   **Formalization Note** Loops that terminate on every valid heap (cascading cuts, repeated linking) carry a step budget of $n+1$, which is never exhausted because depths and degrees are below $n$.
--
--   **Representation and cost convention.** Maps and lists specify the contents of indexed pointer structures extensionally. Known-handle erasure denotes pointer unlinking, list lengths denote cached degrees, and adjacency/subtree enumeration uses the stored incidence/child links. Charges count the corresponding source pointer operations in constant-size groups; processed/scanned sets are ghost observations. This cost is separate from evaluating Lean’s functional representation.
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), §5 'Global queue', PDF p.7 = printed p.7; Appendix B.1, PDF p.16 = printed p.16; reference [6] (Fredman–Tarjan)

import Mathlib

open scoped ENNReal

namespace ExactDynamicSSSP.ExpectedUpdate

noncomputable section

/-! # An indexed Fibonacci heap with instrumented actual work

The global propagation container `C_main` of the paper is a Fibonacci heap (§5 "Global
queue", PDF p. 7; Appendix B.1, p. 16; Fredman–Tarjan, JACM 34(3), 1987). This file gives a
concrete indexed Fibonacci heap on the handles `Fin n` with keys in `[0, ∞]`, following the
standard operations (insert into the root list, decrease-key with cut and cascading cut,
delete-min with consolidation by degree). Every operation returns the new heap together with
its **actual work**: one unit per root-list insertion, key comparison, link, cut, root scan,
moved child and degree-table slot scanned. Nothing in this file is an amortized bound; the
amortized analysis is a theorem about these counts.

Maps and lists describe the contents of indexed handle tables and doubly linked lists.
`erase x` specifies unlinking a known handle, not a linear search; list lengths describe cached
degrees, and the bulk updates on promoted children describe the charged child loop. Charges
count constant-size groups of pointer operations and comparisons in this model, not the time
taken to evaluate the functional Lean representation. In particular root scans, links, moved
children and degree-table scans are charged separately in `deleteMin`.

Loops that a valid heap always finishes (cascading cut, linking equal degrees) are written
with a fuel of `n + 1` steps, which is never exhausted: degrees and depths are below `n`. -/

/-- An indexed Fibonacci heap over the handles `Fin n`. -/
structure FibHeap (n : ℕ) where
  /-- Current key of each handle. -/
  key : Fin n → ℝ≥0∞
  /-- Whether the handle is currently in the heap. -/
  present : Fin n → Bool
  /-- Heap-tree parent (`none` for a root). -/
  parent : Fin n → Option (Fin n)
  /-- Heap-tree children, most recently linked first. -/
  children : Fin n → List (Fin n)
  /-- Mark bit (a non-root that has lost a child). -/
  marked : Fin n → Bool
  /-- The root list. -/
  roots : List (Fin n)
  /-- The minimum pointer (`none` iff the heap is empty). -/
  minimum : Option (Fin n)

namespace FibHeap

variable {n : ℕ}

/-- The empty heap. -/
def empty : FibHeap n :=
  ⟨fun _ => ⊤, fun _ => false, fun _ => none, fun _ => [], fun _ => false, [], none⟩

/-- Point the minimum pointer at the root `x` if its key is strictly smaller (one comparison). -/
def offerMin (h : FibHeap n) (x : Fin n) : FibHeap n :=
  match h.minimum with
  | none => { h with minimum := some x }
  | some m => if h.key x < h.key m then { h with minimum := some x } else h

/-- `insert`: add a new singleton tree with key `k` to the root list. Actual work `1`. -/
def insert (h : FibHeap n) (x : Fin n) (k : ℝ≥0∞) : FibHeap n × ℕ :=
  let h1 : FibHeap n :=
    { h with key := Function.update h.key x k, present := Function.update h.present x true,
             parent := Function.update h.parent x none, children := Function.update h.children x [],
             marked := Function.update h.marked x false, roots := x :: h.roots }
  (offerMin h1 x, 1)

/-- Cut `x` from its parent `p` and make it an unmarked root. Actual work `1`. -/
def cut (h : FibHeap n) (x p : Fin n) : FibHeap n :=
  { h with children := Function.update h.children p ((h.children p).erase x),
           parent := Function.update h.parent x none,
           marked := Function.update h.marked x false,
           roots := x :: h.roots }

/-- Cascading cut starting at `y` (whose child has just been cut): stop at a root, mark an
unmarked non-root, or cut a marked non-root and continue at its parent. Returns the heap and
the number of cuts performed. -/
def cascadingCut : ℕ → FibHeap n → Fin n → FibHeap n × ℕ
  | 0, h, _ => (h, 0)
  | fuel + 1, h, y =>
    match h.parent y with
    | none => (h, 0)
    | some z =>
      if h.marked y then
        let r := cascadingCut fuel (h.cut y z) z
        (r.1, r.2 + 1)
      else ({ h with marked := Function.update h.marked y true }, 0)

/-- `decrease-key`: lower the key of the present handle `x` to `k ≤ key x`. If heap order is
violated, cut `x` and run the cascading cut. Actual work: `1` for a root (key write and minimum
comparison); `2` for a non-root in heap order (key write, order test); `3` plus one per cascading
cut when `x` is cut (key write, order test, the cut and minimum comparison). -/
def decreaseKey (h : FibHeap n) (x : Fin n) (k : ℝ≥0∞) : FibHeap n × ℕ :=
  let h1 : FibHeap n := { h with key := Function.update h.key x k }
  match h1.parent x with
  | none => (offerMin h1 x, 1)
  | some p =>
    if k < h1.key p then
      let r := cascadingCut (n + 1) (h1.cut x p) p
      (offerMin r.1 x, 3 + r.2)
    else (h1, 2)

/-- Make the root `c` a child of the root `p` (`FIB-HEAP-LINK`). -/
def link (h : FibHeap n) (c p : Fin n) : FibHeap n :=
  { h with parent := Function.update h.parent c (some p),
           marked := Function.update h.marked c false,
           children := Function.update h.children p (c :: h.children p) }

/-- Put the detached root `r` of degree `d` into the degree table, linking it with the root
already stored at that degree (the larger key becomes the child; on equal keys `r` stays the
root) and repeating at the next degree. Returns the heap, the table, the final degree and the
number of links. -/
def tableInsert : ℕ → FibHeap n → (ℕ → Option (Fin n)) → Fin n → ℕ →
    FibHeap n × (ℕ → Option (Fin n)) × ℕ × ℕ
  | 0, h, t, r, d => (h, Function.update t d (some r), d, 0)
  | fuel + 1, h, t, r, d =>
    match t d with
    | none => (h, Function.update t d (some r), d, 0)
    | some o =>
      let t' := Function.update t d none
      let top := if h.key o < h.key r then o else r
      let bot := if h.key o < h.key r then r else o
      let res := tableInsert fuel (h.link bot top) t' top (d + 1)
      (res.1, res.2.1, res.2.2.1, res.2.2.2 + 1)

/-- Consolidation, first pass: scan the roots one at a time and insert them into the degree
table. Returns the heap, the table, the number of table slots in use (one more than the
largest degree reached) and the work (one per root scanned plus one per link). -/
def consolidateRoots (fuel : ℕ) : List (Fin n) → FibHeap n → (ℕ → Option (Fin n)) → ℕ → ℕ →
    FibHeap n × (ℕ → Option (Fin n)) × ℕ × ℕ
  | [], h, t, slots, c => (h, t, slots, c)
  | r :: rs, h, t, slots, c =>
    let res := tableInsert fuel h t r (h.children r).length
    consolidateRoots fuel rs res.1 res.2.1 (max slots (res.2.2.1 + 1)) (c + 1 + res.2.2.2)

/-- `delete-min`: remove the minimum root, move its children to the root list, consolidate,
and rebuild the root list and minimum pointer by scanning the degree table. Returns the heap,
the extracted handle (`none` on an empty heap) and the actual work: `1`, plus one per moved
child, plus the consolidation work, plus one per table slot scanned. -/
def deleteMin (h : FibHeap n) : FibHeap n × Option (Fin n) × ℕ :=
  match h.minimum with
  | none => (h, none, 1)
  | some z =>
    let kids := h.children z
    let h1 : FibHeap n :=
      { h with present := Function.update h.present z false,
               children := Function.update h.children z [],
               parent := fun y => if y ∈ kids then none else h.parent y,
               marked := fun y => if y ∈ kids then false else h.marked y,
               roots := [], minimum := none }
    let res := consolidateRoots (n + 1) (h.roots.erase z ++ kids) h1 (fun _ => none) 0 0
    let newRoots := (List.range res.2.2.1).filterMap res.2.1
    let h2 : FibHeap n := newRoots.foldl offerMin { res.1 with roots := newRoots }
    (h2, some z, 1 + kids.length + res.2.2.2 + res.2.2.1)

end FibHeap

end

end ExactDynamicSSSP.ExpectedUpdate


