-- Prove2me | solution 1 for Algo2Lean.UnionFind.Operations.from_initial
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:00:23.147441+00:00
-- url     : https://prove2.me/submissions/0e961fc1-f01b-499b-9676-99192b82ece2

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_Operations_amortized


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Union-find mathematics for implementations using union by rank.

The parent and rank maps describe the stored data. Representatives and masses
are proof-only witnesses: a root owns the mass of its component, and linking
two roots transfers all losing mass to the winner. Starting from singleton
components gives a fixed mass budget of `n`. A root of rank `r` owns at least
`2 ^ r` mass, so every find follows at most `log₂ n` parent links.

Path compression preserves these bounds and the represented partition. The
module proves a logarithmic worst-case bound, not an inverse-Ackermann amortized
bound. It imports no generated algorithm or execution model.
-/

namespace Algo2Lean.UnionFind









theorem total_ones (n : Nat) : total (n := n) (fun _ => 1) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih, Nat.add_comm]













theorem initial_valid (n : Nat) : Valid (initial n) := by
  constructor
  · intro vertex; rfl
  · intro vertex _; rfl
  · intro vertex; rfl
  · intro vertex different; exact False.elim (different rfl)
  · intro vertex _; simp [initial]
  · intro vertex different; exact False.elim (different rfl)
  · simp [initial, total_ones]





















































end Algo2Lean.UnionFind

end

section
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





























open Algo2Lean.Ackermann

noncomputable section



















































































-- Main result: Running time
/-- Starting with singleton sets, the total cost of any finite sequence is
    bounded by its find and union counts times genuine inverse-Ackermann budgets. -/
theorem Operations.from_initial {n : Nat} {after : State n} {finds unions cost : Nat}
    (operations : Operations (initial n) after finds unions cost) :
    cost ≤ finds * (2 * alpha n + 3) + unions * (6 * alpha n + 7) := by
  have budget := (operations.amortized (initial_valid n)).2
  rw [initial_potential] at budget
  omega



end
end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {after : Algo2Lean.UnionFind.State n} {finds unions cost : Nat},
      Algo2Lean.UnionFind.Operations (Algo2Lean.UnionFind.initial n) after finds unions cost →
        LE.le.{0} cost
          (HAdd.hAdd.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} finds
              (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n))
                (3 : Nat)))
            (HMul.hMul.{0, 0, 0} unions
              (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n))
                (7 : Nat)))) :=
  Algo2Lean.UnionFind.Operations.from_initial
