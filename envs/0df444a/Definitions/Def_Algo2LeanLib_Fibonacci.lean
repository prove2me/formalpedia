-- Prove2me | Definitions.Def_Algo2LeanLib_Fibonacci
-- name    : Algo2LeanLib_Fibonacci
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:38:55.49891+00:00
-- url     : https://prove2.me/theorems/45f93022-de9b-4b0f-9969-e88946111c0b
-- title:
--   Algo2LeanLib.Fibonacci definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.Fibonacci`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Fibonacci.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Mathematical building blocks for Fibonacci heaps.

The tree lemmas use children in reverse link order (newest first). The rank
invariant records the consequence of equal-degree links and cutting a nonroot
when it loses its second child. The accounting relations describe actual
root/mark changes; they do not assume their amortized bounds.

This module is independent of any generated program. A compiled implementation
must separately establish the rank invariant and realize the accounting steps.
References: Fredman and Tarjan, JACM 34(3), 1987; David Karger's MIT 6.854 notes,
https://courses.csail.mit.edu/6.854/21/Notes/n01-fibonacci.html.
-/

namespace Algo2Lean.Fibonacci

/-- `minimumNodes degree` is the Fibonacci number F(degree + 2). -/
def minimumNodes : Nat → Nat
  | 0 => 1
  | 1 => 2
  | degree + 2 => minimumNodes (degree + 1) + minimumNodes degree

@[simp] theorem minimumNodes_zero : minimumNodes 0 = 1 := rfl
@[simp] theorem minimumNodes_one : minimumNodes 1 = 2 := rfl











/-- Tree shape only; keys and addresses do not affect the rank argument. -/
inductive Tree where
  | node : List Tree → Tree

def Tree.degree : Tree → Nat
  | .node children => children.length

def Tree.nodes : Tree → Nat
  | .node children => 1 + (children.map Tree.nodes).sum

/-- Each child's degree is at least its number of older siblings minus one.
    Newest-first order models equal-degree links followed by at most one child loss. -/
def RankOrder : List Tree → Prop
  | [] => True
  | child :: older => older.length ≤ child.degree + 1 ∧ RankOrder older

inductive Tree.Ranked : Tree → Prop where
  | node {children : List Tree} : RankOrder children →
    (∀ child ∈ children, Tree.Ranked child) → Tree.Ranked (.node children)













def Tree.link (parent child : Tree) : Tree :=
  match parent with
  | .node children => .node (child :: children)



@[simp] theorem Tree.link_degree (parent child : Tree) :
    (parent.link child).degree = parent.degree + 1 := by cases parent; rfl

@[simp] theorem Tree.link_nodes (parent child : Tree) :
    (parent.link child).nodes = parent.nodes + child.nodes := by
  cases parent
  simp [Tree.link, Tree.nodes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]





/-- Counts used by the standard Fibonacci-heap potential. Marks count marked
    nonroots; adding a root clears its mark. -/
structure Counts where
  roots : Nat
  marks : Nat
  deriving DecidableEq

def potential (counts : Counts) : Nat := counts.roots + 2 * counts.marks

def scaledPotential (counts : Counts) : Nat := 4 * potential counts

/-- Cascade after a child was cut: stop at a root, mark an unmarked nonroot,
    or cut a marked nonroot and continue at its parent. -/
inductive Cascade : Counts → Counts → Nat → Prop where
  | root (state : Counts) : Cascade state state 0
  | mark (roots marks : Nat) : Cascade ⟨roots, marks⟩ ⟨roots, marks + 1⟩ 0
  | cut {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Cascade ⟨roots, marks + 1⟩ after (cuts + 1)



/-- A decrease either makes no cut, or cuts the requested node (which may or
    may not have been marked) and then follows the cascading-cut rule. -/
inductive Decrease : Counts → Counts → Nat → Prop where
  | unchanged (state : Counts) : Decrease state state 0
  | unmarked {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Decrease ⟨roots, marks⟩ after (cuts + 1)
  | marked {roots marks cuts : Nat} {after : Counts} :
      Cascade ⟨roots + 1, marks⟩ after cuts → Decrease ⟨roots, marks + 1⟩ after (cuts + 1)







/-- Consolidation repeatedly links two roots into one. Existing roots are
    unmarked, so the operation preserves the number of marked nonroots. -/
inductive Consolidation : Counts → Counts → Nat → Prop where
  | done (state : Counts) : Consolidation state state 0
  | link {roots marks links : Nat} {after : Counts} (remainingRoot : 0 < roots) :
      Consolidation ⟨roots, marks⟩ after links → Consolidation ⟨roots + 1, marks⟩ after (links + 1)





/-- Explicit event counts for one extraction, before any amortized argument.
    Root scans visit the promoted forest once; links compare their roots;
    rebuilding visits the degree table and compares its surviving roots. -/
structure ExtractEvents where
  rootScans : Nat
  links : Nat
  promotions : Nat
  degreeScans : Nat
  comparisons : Nat

def ExtractEvents.work (events : ExtractEvents) : Nat :=
  1 + events.rootScans + events.links + events.promotions + events.degreeScans + events.comparisons







/-- Abstract operation accounting with local, independently checkable events.
    `updates` counts insert/decrease calls; `extractions` counts delete-min calls.
    Extraction requires explicit bounds on the promoted degree, final root count,
    table scans, and comparisons; these are premises of the operation relation. -/
inductive Operation (maximumDegree : Nat) : Counts → Counts → Nat → Nat → Nat → Prop where
  | insert (roots marks work : Nat) (events : work ≤ 2) :
      Operation maximumDegree ⟨roots, marks⟩ ⟨roots + 1, marks⟩ work 1 0
  | decrease {before after : Counts} {cuts work : Nat}
      (cascade : Decrease before after cuts) (events : work ≤ 4 * cuts + 4) :
      Operation maximumDegree before after work 1 0
  | extract (before promoted after : Counts) (degree : Nat) (events : ExtractEvents)
      (promotedRoots : promoted.roots + 1 = before.roots + degree)
      (clearedMarks : promoted.marks ≤ before.marks)
      (consolidation : Consolidation promoted after events.links)
      (degreeBound : degree ≤ maximumDegree) (finalRoots : after.roots ≤ maximumDegree + 1)
      (scanBound : events.rootScans ≤ promoted.roots)
      (promotionCount : events.promotions = degree)
      (tableBound : events.degreeScans ≤ maximumDegree + 1)
      (comparisonBound : events.comparisons ≤ degree + events.links + after.roots) :
      Operation maximumDegree before after events.work 0 1



/-- A finite sequence of modeled heap operations. The clock total and numbers
    of update/extract calls are sums of the concrete operation events. -/
inductive Run (maximumDegree : Nat) : Counts → Counts → Nat → Nat → Nat → Prop where
  | empty (state : Counts) : Run maximumDegree state state 0 0 0
  | step {before middle after : Counts} {work updates extractions tailWork tailUpdates tailExtractions : Nat} :
      Operation maximumDegree before middle work updates extractions →
      Run maximumDegree middle after tailWork tailUpdates tailExtractions →
      Run maximumDegree before after (work + tailWork) (updates + tailUpdates) (extractions + tailExtractions)







end Algo2Lean.Fibonacci


