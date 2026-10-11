-- Prove2me | Definitions.Def_Algo2LeanLib_UnionFindAmortized
-- name    : Algo2LeanLib_UnionFindAmortized
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:23.850386+00:00
-- url     : https://prove2.me/theorems/0f7545fa-61f9-470c-a4aa-6977f18a4653
-- title:
--   Union-find model: Ackermann potential and mixed-operation costs
-- statement:
--   This bundle defines full-path compression, Ackermann-level credits, the nonnegative potential **`Algo2Lean.UnionFind.potential`**, and the pure mixed-operation relation `Operations`. The exact inverse function is imported from the separate **Ackermann hierarchy and inverse-Ackermann function** definition bundle under `Algo2Lean.Ackermann.alpha`.
--
--   For a node of rank $r$ with parent rank $p$, `level` and `iterations` measure progress through the Ackermann hierarchy. A root has credit $\alpha(n)r$; a positive-rank nonroot's credit subtracts its attained progress from that amount, while rank-zero nodes contribute zero. `potential` sums these natural-number credits over the finite universe. The initial singleton potential is zero.
--
--   `Operations before after f u C` counts explicit find operations, union operations and charged source events. A find along $p$ nonroot edges costs $2p+1$; a union whose two finds traverse $p,q$ edges costs $2(p+q)+3$. The two internal finds are included in the union charge, not in $f$. Constructor cost is separate. The relation is a mathematical model; separate compiled contracts tie it to heap mutation and ticks. Nontrivial amortized results are separate theorem nodes, including `compressPath_amortized`, `Operations.amortized` and `Operations.from_initial`.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/UnionFindAmortized.lean

import Definitions.Def_Algo2LeanLib_UnionFind
import Definitions.Def_Algo2LeanLib_Ackermann

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Inverse-Ackermann amortized analysis for union by rank and full path compression.

The Ackermann hierarchy and its least positive inverse are defined and proved
in `Algo2LeanLib.Ackermann`. This module uses the rank/level/iteration potential
argument of Cormen, Leiserson, Rivest, and Stein, Introduction to Algorithms,
second edition, §21.4. All definitions and proofs below are independent of
compiled programs and their heap representation.

A positive-rank nonroot records the largest Ackermann level below its parent's
rank and the number of iterations reached within that level. Its credit is
`alpha(n) * rank - (level * rank + iterations)`; a root has `alpha(n) * rank`
credit. A rank-zero node has zero credit. The global potential sums these
nonnegative credits over the fixed universe.

Path compression increases a node's hierarchy progress whenever its old level
occurs again later on the path. All but at most one rank-zero node and one node
per level therefore pay for their own traversed edge. A rank link can increase
credit only at the winning root, by at most `alpha(n)`. Scaling the potential
by two pays for both the find and compression events in the source cost model.

The reusable local results are `find_amortized` and `union_amortized`.
`Operations.from_initial` telescopes their bounds across arbitrary finite
operation sequences; `Operations.total_cost` includes initialization and gives
`n + 1 + 13 * (finds + unions) * alpha(n)`. The logarithmic worst-case bound
for an individual operation remains available from `Algo2LeanLib.UnionFind`.
-/

namespace Algo2Lean.UnionFind

/-- Redirect a traversed parent path to its representative, on recursive return. -/
def compressPath {n : Nat} (state : State n) (vertex : Fin n) : Nat → State n
  | 0 => state
  | steps + 1 => compress (compressPath state (state.parent vertex) steps) vertex

@[simp] theorem compressPath_representative {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).representative = state.representative := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)

@[simp] theorem compressPath_rank {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).rank = state.rank := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)

@[simp] theorem compressPath_mass {n : Nat} (state : State n) (vertex : Fin n)
    (steps : Nat) : (compressPath state vertex steps).mass = state.mass := by
  induction steps generalizing vertex with
  | zero => rfl
  | succ steps ih => exact ih (state.parent vertex)



/-- Largest successful natural index within a finite search bound, defaulting to zero. -/
def boundedMax (test : Nat → Bool) : Nat → Nat
  | 0 => 0
  | bound + 1 => if test (bound + 1) then bound + 1 else boundedMax test bound

















open Algo2Lean.Ackermann

noncomputable section

/-- Highest Ackermann level reached by a positive rank's parent rank. -/
def level (size rank parentRank : Nat) : Nat :=
  boundedMax (fun index => decide (ack index rank ≤ parentRank)) (alpha size)

/-- Number of iterations at the node's current Ackermann level. -/
def iterations (size rank parentRank : Nat) : Nat :=
  boundedMax (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1)

















/-- Progress within the hierarchy: increasing the level outweighs resetting its iteration. -/
def progress (size rank parentRank : Nat) : Nat :=
  level size rank parentRank * rank + iterations size rank parentRank







/-- CLRS credit: roots own alpha times rank; a nonroot spends credit on its level and iteration. -/
def credit (size rank parentRank : Nat) : Nat :=
  if rank = 0 ∨ parentRank ≤ rank then alpha size * rank
  else alpha size * rank - progress size rank parentRank

@[simp] theorem credit_zero (size parentRank : Nat) : credit size 0 parentRank = 0 := by
  simp [credit]

@[simp] theorem credit_root (size rank : Nat) : credit size rank rank = alpha size * rank := by
  simp [credit]







/-- Sum of the nonnegative node credits in the current finite universe. -/
def potential {n : Nat} (state : State n) : Nat :=
  total (fun vertex => credit n (state.rank vertex) (state.rank (state.parent vertex)))

@[simp] theorem initial_potential (n : Nat) : potential (initial n) = 0 := by
  unfold potential
  have zeros : ∀ n, total (n := n) (fun _ => 0) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  simpa [initial] using zeros n











/-- Number of distinct path levels, counted in the finite range below alpha. -/
def levelCount (size : Nat) (levels : List Nat) : Nat :=
  total (fun index : Fin (alpha size) => if index.val ∈ levels then 1 else 0)



@[simp] theorem levelCount_nil (size : Nat) : levelCount size [] = 0 := by
  have zeros : ∀ n, total (n := n) (fun _ => 0) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [total, ih]
  simpa [levelCount] using zeros (alpha size)





/-- The old levels of positive-rank nonroot vertices on a given traversal. -/
def pathLevels {n : Nat} (state : State n) (vertex : Fin n) : Nat → List Nat
  | 0 => []
  | steps + 1 =>
      let tail := pathLevels state (state.parent vertex) steps
      if state.rank vertex = 0 then tail
      else level n (state.rank vertex) (state.rank (state.parent vertex)) :: tail













/-- A finite mixed sequence of finds and unions. The last three indices count
    find calls, union calls, and the source events charged by those operations. -/
inductive Operations {n : Nat} : State n → State n → Nat → Nat → Nat → Prop where
  | done (state : State n) : Operations state state 0 0 0
  | find {state final : State n} {vertex root : Fin n} {steps finds unions cost : Nat}
      (path : Find state vertex root steps)
      (rest : Operations (compressPath state vertex steps) final finds unions cost) :
      Operations state final (finds + 1) unions ((2 * steps + 1) + cost)
  | union {state final : State n} {first second firstRoot secondRoot : Fin n}
      {firstSteps secondSteps finds unions cost : Nat}
      (firstPath : Find state first firstRoot firstSteps)
      (secondPath : Find (compressPath state first firstSteps) second secondRoot secondSteps)
      (rest : Operations
        (union (compressPath (compressPath state first firstSteps) second secondSteps) first second)
        final finds unions cost) :
      Operations state final finds (unions + 1) ((2 * (firstSteps + secondSteps) + 3) + cost)



-- Main result: Running time




end
end Algo2Lean.UnionFind


