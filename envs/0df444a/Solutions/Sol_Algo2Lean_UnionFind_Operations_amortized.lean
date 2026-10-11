-- Prove2me | solution 1 for Algo2Lean.UnionFind.Operations.amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:56:52.552839+00:00
-- url     : https://prove2.me/submissions/3c45fbbc-9c86-440b-89f7-2bbd494512b9

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_compress_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_valid
import Theorems.Thm_Algo2Lean_UnionFind_link_potential
import Theorems.Thm_Algo2Lean_UnionFind_compressPath_amortized


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





































































/-- Union preserves the forest representation and rank/mass accounting. -/
theorem union_valid {n : Nat} {state : State n} (valid : Valid state)
    (first second : Fin n) : Valid (union state first second) := by
  simp only [union]
  split
  · exact valid
  · rename_i different
    split
    · rename_i ordered
      exact link_valid valid _ _ different (valid.representative_root first)
        (valid.representative_root second) (by omega)
    · rename_i ordered
      exact link_valid valid _ _ (Ne.symm different) (valid.representative_root second)
        (valid.representative_root first) (by omega)







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









/-- The structural invariant is preserved by every finite sequence of compression writes. -/
theorem compressPath_valid {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) (steps : Nat) : Valid (compressPath state vertex steps) := by
  induction steps generalizing vertex with
  | zero => exact valid
  | succ steps ih => exact compress_valid (ih (state.parent vertex)) vertex



















open Algo2Lean.Ackermann

noncomputable section





















































/-- Choosing the rank-ordered orientation does not affect the alpha-sized link budget. -/
theorem union_potential {n : Nat} {state : State n} (valid : Valid state) (first second : Fin n) :
    potential (union state first second) ≤ potential state + alpha n := by
  simp only [union]
  split
  · omega
  · rename_i different
    split
    · rename_i ordered
      exact link_potential valid _ _ different (valid.representative_root first)
        (valid.representative_root second) (by omega)
    · rename_i ordered
      exact link_potential valid _ _ (Ne.symm different) (valid.representative_root second)
        (valid.representative_root first) (by omega)





















/-- Scaling credits by two pays one root test plus both events on every nonroot step. -/
theorem find_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    (2 * steps + 1) + 2 * potential (compressPath state vertex steps) ≤
      2 * potential state + 2 * alpha n + 3 := by
  have charged := compressPath_amortized valid path
  omega

/-- Two compressed finds followed by a rank link have inverse-Ackermann amortized cost. -/
theorem union_amortized {n : Nat} {state : State n} (valid : Valid state)
    {first second firstRoot secondRoot : Fin n} {firstSteps secondSteps : Nat}
    (firstPath : Find state first firstRoot firstSteps)
    (secondPath : Find (compressPath state first firstSteps) second secondRoot secondSteps) :
    (2 * (firstSteps + secondSteps) + 3) +
        2 * potential (union (compressPath (compressPath state first firstSteps) second secondSteps) first second) ≤
      2 * potential state + 6 * alpha n + 7 := by
  have firstBudget := find_amortized valid firstPath
  have middleValid := compressPath_valid valid first firstSteps
  have secondBudget := find_amortized middleValid secondPath
  have finalValid := compressPath_valid middleValid second secondSteps
  have linkBudget := union_potential finalValid first second
  omega



/-- Local potential budgets telescope across an arbitrary mixed operation sequence. -/
theorem Operations.amortized {n : Nat} {before after : State n} {finds unions cost : Nat}
    (operations : Operations before after finds unions cost) (valid : Valid before) :
    Valid after ∧ cost + 2 * potential after ≤ 2 * potential before +
      finds * (2 * alpha n + 3) + unions * (6 * alpha n + 7) := by
  induction operations with
  | done state => exact ⟨valid, by simp⟩
  | find path rest ih =>
    obtain ⟨finalValid, remaining⟩ := ih (compressPath_valid valid _ _)
    have current := find_amortized valid path
    refine ⟨finalValid, ?_⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  | union firstPath secondPath rest ih =>
    obtain ⟨finalValid, remaining⟩ :=
      ih (union_valid (compressPath_valid (compressPath_valid valid _ _) _ _) _ _)
    have current := union_amortized valid firstPath secondPath
    refine ⟨finalValid, ?_⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega

-- Main result: Running time




end
end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {before after : Algo2Lean.UnionFind.State n} {finds unions cost : Nat},
      Algo2Lean.UnionFind.Operations before after finds unions cost →
        Algo2Lean.UnionFind.Valid before →
          Algo2Lean.UnionFind.Valid after ∧
            LE.le.{0}
              (HAdd.hAdd.{0, 0, 0} cost
                (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential after)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.UnionFind.potential before))
                  (HMul.hMul.{0, 0, 0} finds
                    (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Nat) (Algo2Lean.Ackermann.alpha n))
                      (3 : Nat))))
                (HMul.hMul.{0, 0, 0} unions
                  (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (6 : Nat) (Algo2Lean.Ackermann.alpha n))
                    (7 : Nat)))) :=
  Algo2Lean.UnionFind.Operations.amortized
