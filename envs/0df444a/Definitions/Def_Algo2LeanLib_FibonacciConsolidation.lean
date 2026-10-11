-- Prove2me | Definitions.Def_Algo2LeanLib_FibonacciConsolidation
-- name    : Algo2LeanLib_FibonacciConsolidation
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:59.798691+00:00
-- url     : https://prove2.me/theorems/b414f449-9dd4-4e4c-9f64-67430929154e
-- title:
--   Algo2LeanLib.FibonacciConsolidation definitions
-- statement:
--   Definitions and required structural lemmas from `Algo2LeanLib.FibonacciConsolidation`. Source declarations are retained by compiler-reported ranges; imports are redirected to the corresponding definition bundles. This bundle contains no theorem stubs.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/FibonacciConsolidation.lean

import Definitions.Def_Algo2LeanLib_FibonacciStorage

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Algo2Lean.Fibonacci

/-- Detach the cursor root, keeping the remaining root ring as pending work. -/
def Snapshot.detachMinimum (state : Snapshot) : Snapshot :=
  {state with
    left := Rings.removeLeft state.left state.right state.minimum
    right := Rings.removeRight state.left state.right state.minimum
    minimum := if state.right state.minimum = state.minimum then -1 else state.right state.minimum}
















/-- Finite ghost contents of the scratch table, with exactly one root per degree. -/
structure Buckets (state : Snapshot) (roots : Forest) : Prop where
  unique : (roots.map Node.degree).Nodup
  read : ∀ root ∈ roots, state.table root.degree = root.vertex
  complete : ∀ degree, 0 ≤ state.table degree →
    ∃ root ∈ roots, (root.degree : Int) = degree ∧ root.vertex = state.table degree
  nonnegative : ∀ root ∈ roots, 0 ≤ root.vertex
























/-- The exact array operation for a degree-table collision; clocks are separate. -/
def Snapshot.collision (state : Snapshot) (vertex degree : Int) : Snapshot :=
  let other := state.table degree
  let cleared := {state with table := Rings.write state.table degree (-1)}
  if state.keys other < state.keys vertex then cleared.link vertex other
  else cleared.link other vertex

def Snapshot.collisionParent (state : Snapshot) (vertex degree : Int) : Int :=
  if state.keys (state.table degree) < state.keys vertex then state.table degree else vertex

@[simp] theorem Node.link_vertex (parent child : Node) : (parent.link child).vertex = parent.vertex := rfl
@[simp] theorem Node.link_degree (parent child : Node) : (parent.link child).degree = parent.degree + 1 := rfl



/-- A trace of scratch-table collisions records only exact local array effects. -/
inductive BucketCollisions : Snapshot → Int → Int → Snapshot → Int → Int → Nat → Prop where
  | done (state : Snapshot) (vertex degree : Int) (empty : state.table degree < 0) :
      BucketCollisions state vertex degree state vertex degree 0
  | step {state after : Snapshot} {vertex degree result finalDegree : Int} {links : Nat}
      (occupied : 0 ≤ state.table degree)
      (rest : BucketCollisions (state.collision vertex degree) (state.collisionParent vertex degree)
        (degree + 1) after result finalDegree links) :
      BucketCollisions state vertex degree after result finalDegree (links + 1)






/-- The highest encountered degree bounds all occupied scratch buckets. -/
def ScratchBound (state : Snapshot) (maximum : Int) : Prop :=
  ∀ degree, maximum < degree → state.table degree < 0

@[simp] theorem Snapshot.collision_table (state : Snapshot) (vertex degree : Int) :
    (state.collision vertex degree).table = Rings.write state.table degree (-1) := by
  unfold Snapshot.collision
  dsimp only
  split <;> rfl

@[simp] theorem Snapshot.collision_size (state : Snapshot) (vertex degree : Int) :
    (state.collision vertex degree).size = state.size := by
  unfold Snapshot.collision
  dsimp only
  split <;> rfl











/-- Finite execution of the pending-root phase, expressed through the exact
    snapshot mutations and the independently verified collision phase. -/
inductive RootConsumption : Snapshot → Int → Snapshot → Int → Nat → Nat → Prop where
  | done (state : Snapshot) (maximum : Int) (empty : state.minimum < 0) :
      RootConsumption state maximum state maximum 0 0
  | step {before merged after : Snapshot} {maximum vertex degree finalMaximum : Int}
      {links roots tailLinks : Nat} (nonempty : 0 ≤ before.minimum)
      (collisions : BucketCollisions before.detachMinimum before.minimum
        (before.detachMinimum.degrees before.minimum) merged vertex degree links)
      (rest : RootConsumption {merged with table := Rings.write merged.table degree vertex}
        (max maximum degree) after finalMaximum roots tailLinks) :
      RootConsumption before maximum after finalMaximum (roots + 1) (links + tailLinks)




end Algo2Lean.Fibonacci


