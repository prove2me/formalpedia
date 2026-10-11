-- Prove2me | solution 1 for Algo2Lean.UnionFind.link_potential
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:55:30.10477+00:00
-- url     : https://prove2.me/submissions/e959740c-4ce7-4681-9b26-537739c4ac45

import Definitions.Def_Algo2LeanLib_UnionFindAmortized
import Theorems.Thm_Algo2Lean_UnionFind_link_valid


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











theorem entry_le_total {n : Nat} (f : Fin n → Nat) (vertex : Fin n) :
    f vertex ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 vertex
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) vertex
    · simp [total]
    · have bound := ih (fun index => f index.succ) index
      change f index.succ ≤ f 0 + total (fun index => f index.succ)
      omega

theorem total_update {n : Nat} (f : Fin n → Nat) (index : Fin n) (value : Nat) :
    total (update f index value) + f index = total f + value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [total, update, Fin.succ_ne_zero, Nat.add_comm, Nat.add_left_comm]
    · have next := ih (fun index => f index.succ) index
      simpa [total, update, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero index), Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using! congrArg (fun x => f 0 + x) next















theorem find_correct {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (run : Find state vertex root steps) :
    root = state.representative vertex ∧ state.parent root = root ∧
      state.rank vertex + steps ≤ state.rank root := by
  induction run with
  | root vertex fixed => exact ⟨(valid.root_representative vertex fixed).symm, fixed, by simp⟩
  | step vertex root steps moving _ ih =>
    obtain ⟨correct, fixed, bound⟩ := ih
    have rising := valid.parent_rank vertex moving
    exact ⟨correct.trans (valid.parent_representative vertex), fixed, by omega⟩

theorem root_rank_le_log {n : Nat} {state : State n} (valid : Valid state)
    (root : Fin n) (fixed : state.parent root = root) : state.rank root ≤ Nat.log2 n := by
  have massBound := Nat.le_trans (entry_le_total state.mass root) valid.mass_budget
  apply (Nat.le_log2 (by have := root.isLt; omega : n ≠ 0)).mpr
  exact Nat.le_trans (valid.root_mass root fixed) massBound



/-- Every valid forest admits a finite find traversal. -/
theorem find_exists {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : ∃ steps, Find state vertex (state.representative vertex) steps := by
  by_cases fixed : state.parent vertex = vertex
  · exact ⟨0, by simpa [valid.root_representative vertex fixed] using Find.root vertex fixed⟩
  · obtain ⟨steps, run⟩ := find_exists valid (state.parent vertex)
    exact ⟨steps + 1, Find.step vertex _ steps fixed
      (by simpa [valid.parent_representative vertex] using run)⟩
termination_by total state.rank - state.rank vertex
decreasing_by
  have rising := valid.parent_rank vertex fixed
  have bounded := entry_le_total state.rank (state.parent vertex)
  omega

theorem rank_le_representative {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : state.rank vertex ≤ state.rank (state.representative vertex) := by
  obtain ⟨steps, run⟩ := find_exists valid vertex
  have := (find_correct valid run).2.2
  omega

















theorem link_rank_ge {n : Nat} (state : State n) (loser winner vertex : Fin n) :
    state.rank vertex ≤ (link state loser winner).rank vertex := by
  by_cases same : vertex = winner
  · subst vertex
    simp only [link, update_same]
    split <;> omega
  · simp [link, update, same]





















end Algo2Lean.UnionFind

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The Ackermann hierarchy used in the union-find amortized analysis.
`ack 0 r = r + 1` and `ack (k + 1) r` applies `ack k` exactly `r + 1`
times to `r`. The inverse `alpha n` is the least positive hierarchy index
whose value at one exceeds `n`. All arithmetic facts are independent of
program execution and of the union-find representation.
-/

namespace Algo2Lean.Ackermann













theorem iterate_strict_start {f : Nat → Nat}
    (strict : ∀ {a b}, a < b → f a < f b) (count : Nat) {a b : Nat} (ordered : a < b) :
    iterate f count a < iterate f count b := by
  induction count with
  | zero => exact ordered
  | succ count ih => exact strict ih











theorem ack_succ (level value : Nat) :
    ack (level + 1) value = iterate (ack level) (value + 1) value := rfl



theorem ack_strict_right (level : Nat) {a b : Nat} (ordered : a < b) :
    ack level a < ack level b := by
  induction level generalizing a b with
  | zero => simpa using ordered
  | succ level ih =>
    have start := iterate_strict_start ih (a + 1) ordered
    have rest := iterate_mono_count (fun x => Nat.le_of_lt (ack_gt level x))
      (Nat.succ_le_succ (Nat.le_of_lt ordered)) b
    exact Nat.lt_of_lt_of_le start rest

theorem ack_mono_right (level : Nat) {a b : Nat} (ordered : a ≤ b) :
    ack level a ≤ ack level b := by
  rcases Nat.eq_or_lt_of_le ordered with same | smaller
  · simp [same]
  · exact Nat.le_of_lt (ack_strict_right level smaller)

















theorem ack_alpha_gt (n : Nat) : n < ack (alpha n) 1 :=
  (Classical.choose_spec (inverse_exists n)).1.2

















end Algo2Lean.Ackermann

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













theorem boundedMax_le (test : Nat → Bool) (bound : Nat) : boundedMax test bound ≤ bound := by
  induction bound with
  | zero => exact Nat.le_refl 0
  | succ bound ih => simp only [boundedMax]; split <;> omega

theorem boundedMax_spec (test : Nat → Bool) (bound : Nat) (zero : test 0 = true) :
    test (boundedMax test bound) = true := by
  induction bound with
  | zero => exact zero
  | succ bound ih => simp only [boundedMax]; split <;> simp_all

theorem le_boundedMax (test : Nat → Bool) (bound index : Nat)
    (within : index ≤ bound) (successful : test index = true) : index ≤ boundedMax test bound := by
  induction bound with
  | zero => omega
  | succ bound ih =>
    simp only [boundedMax]
    split
    · omega
    · rename_i last
      have smaller : index ≤ bound := by
        by_cases smaller : index ≤ bound
        · exact smaller
        · have equal : index = bound + 1 := by omega
          subst index
          exact False.elim (last successful)
      exact ih smaller

theorem boundedMax_upper (test : Nat → Bool) (bound index : Nat)
    (within : index ≤ bound) (above : boundedMax test bound < index) : test index = false := by
  cases success : test index
  · rfl
  · have := le_boundedMax test bound index within success
    omega

/-- Pointwise inequalities lift to sums over the fixed universe. -/
theorem total_mono {n : Nat} {first second : Fin n → Nat}
    (bounded : ∀ vertex, first vertex ≤ second vertex) : total first ≤ total second := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have atZero := bounded 0
    have atRest := ih (fun vertex => bounded vertex.succ)
    simp only [total]
    omega

/-- A pointwise increase confined to one vertex bounds the total increase. -/
theorem total_single_increase {n : Nat} {first second : Fin n → Nat}
    (target : Fin n) (amount : Nat)
    (atTarget : second target ≤ first target + amount)
    (elsewhere : ∀ vertex, vertex ≠ target → second vertex ≤ first vertex) :
    total second ≤ total first + amount := by
  have bounded : total second ≤ total (update first target (first target + amount)) := by
    apply total_mono
    intro vertex
    by_cases same : vertex = target
    · subst vertex; simpa using atTarget
    · simpa [update, same] using elsewhere vertex same
  have replacement := total_update first target (first target + amount)
  omega

/-- Every stored rank is bounded by the fixed universe size. -/
theorem rank_le_size {n : Nat} {state : State n} (valid : Valid state) (vertex : Fin n) :
    state.rank vertex ≤ n :=
  Nat.le_trans (rank_le_representative valid vertex)
    (Nat.le_trans (root_rank_le_log valid _ (valid.representative_root vertex)) (Nat.log2_le_self n))



open Algo2Lean.Ackermann

noncomputable section





theorem level_spec {size rank parentRank : Nat} (rising : rank < parentRank) :
    ack (level size rank parentRank) rank ≤ parentRank := by
  have successful := boundedMax_spec (fun index => decide (ack index rank ≤ parentRank))
    (alpha size) (by simp; omega)
  simpa [level] using successful

theorem level_lt_alpha {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    level size rank parentRank < alpha size := by
  have atLevel := level_spec (size := size) rising
  have upper := boundedMax_le (fun index => decide (ack index rank ≤ parentRank)) (alpha size)
  have beyond := ack_alpha_gt size
  have monotone := ack_mono_right (alpha size) (show 1 ≤ rank by omega)
  change level size rank parentRank ≤ alpha size at upper
  by_cases same : level size rank parentRank = alpha size
  · rw [same] at atLevel
    omega
  · omega

theorem level_next_gt {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    parentRank < ack (level size rank parentRank + 1) rank := by
  have within := level_lt_alpha positive rising bounded
  have failure := boundedMax_upper (fun index => decide (ack index rank ≤ parentRank))
    (alpha size) (level size rank parentRank + 1) (by omega) (by change level _ _ _ < _; omega)
  simpa using failure

theorem iterations_spec {size rank parentRank : Nat} (rising : rank < parentRank) :
    iterate (ack (level size rank parentRank)) (iterations size rank parentRank) rank ≤ parentRank := by
  have successful := boundedMax_spec
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1) (by simp; omega)
  simpa [iterations] using successful



theorem iterations_le_rank {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    iterations size rank parentRank ≤ rank := by
  have successful := iterations_spec (size := size) rising
  have nextLevel := level_next_gt positive rising bounded
  have upper := boundedMax_le
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1)
  change iterations size rank parentRank ≤ rank + 1 at upper
  by_cases same : iterations size rank parentRank = rank + 1
  · rw [same, ← ack_succ] at successful
    omega
  · omega

theorem level_mono {size rank before after : Nat} (rising : rank < before) (grows : before ≤ after) :
    level size rank before ≤ level size rank after := by
  apply le_boundedMax
  · exact boundedMax_le _ _
  · have successful := level_spec (size := size) rising
    simp only [decide_eq_true_eq]
    omega

theorem iterations_mono {size rank before after : Nat} (rising : rank < before)
    (grows : before ≤ after) (sameLevel : level size rank before = level size rank after) :
    iterations size rank before ≤ iterations size rank after := by
  apply le_boundedMax
  · exact boundedMax_le _ _
  · have successful := iterations_spec (size := size) rising
    rw [sameLevel] at successful
    simp only [decide_eq_true_eq]
    omega





theorem progress_mono {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size) :
    progress size rank before ≤ progress size rank after := by
  have levels := level_mono (size := size) rising grows
  by_cases same : level size rank before = level size rank after
  · have counts := iterations_mono rising grows same
    simp only [progress, same]
    omega
  · have counts := iterations_le_rank positive rising (by omega : before ≤ size)
    have product := Nat.mul_le_mul_right rank
      (show level size rank before + 1 ≤ level size rank after by omega)
    simp only [Nat.add_mul, Nat.one_mul] at product
    unfold progress
    omega









theorem credit_le (size rank parentRank : Nat) : credit size rank parentRank ≤ alpha size * rank := by
  unfold credit
  split <;> omega

theorem credit_mono {size rank before after : Nat} (rising : rank < before)
    (grows : before ≤ after) (bounded : after ≤ size) : credit size rank after ≤ credit size rank before := by
  by_cases zero : rank = 0
  · simp [zero]
  · have progress := progress_mono (by omega : 0 < rank) rising grows bounded
    simp only [credit, zero, false_or, if_neg (show ¬ before ≤ rank by omega),
      if_neg (show ¬ after ≤ rank by omega)]
    omega













/-- A rank link can increase the global potential only at its winning root,
    and only by one alpha-sized rank increment. -/
theorem link_potential {n : Nat} {state : State n} (valid : Valid state)
    (loser winner : Fin n) (different : loser ≠ winner)
    (loserRoot : state.parent loser = loser) (winnerRoot : state.parent winner = winner)
    (ordered : state.rank loser ≤ state.rank winner) :
    potential (link state loser winner) ≤ potential state + alpha n := by
  have linkedValid := link_valid valid loser winner different loserRoot winnerRoot ordered
  have winnerFixed : (link state loser winner).parent winner = winner := by
    simp [link, update, different.symm, winnerRoot]
  unfold potential
  apply total_single_increase winner (alpha n)
  · rw [winnerFixed, winnerRoot, credit_root, credit_root]
    have rise : (link state loser winner).rank winner ≤ state.rank winner + 1 := by
      simp only [link, update_same]
      split <;> omega
    have scaled := Nat.mul_le_mul_left (alpha n) rise
    simpa only [Nat.mul_add, Nat.mul_one] using scaled
  · intro vertex notWinner
    have sameRank : (link state loser winner).rank vertex = state.rank vertex := by
      simp [link, update, notWinner]
    rw [sameRank]
    by_cases same : vertex = loser
    · subst vertex
      rw [loserRoot, credit_root]
      exact credit_le _ _ _
    · have sameParent : (link state loser winner).parent vertex = state.parent vertex := by
        simp [link, update, same]
      rw [sameParent]
      by_cases fixed : state.parent vertex = vertex
      · rw [fixed, sameRank]
        exact Nat.le_refl _
      · apply credit_mono (valid.parent_rank vertex fixed)
        · exact link_rank_ge state loser winner (state.parent vertex)
        · exact rank_le_size linkedValid (state.parent vertex)































-- Main result: Running time




end
end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (loser winner : Fin n),
          Ne.{1} loser winner →
            Eq.{1} (state.parent loser) loser →
              Eq.{1} (state.parent winner) winner →
                LE.le.{0} (state.rank loser) (state.rank winner) →
                  LE.le.{0}
                    (Algo2Lean.UnionFind.potential (Algo2Lean.UnionFind.link state loser winner))
                    (HAdd.hAdd.{0, 0, 0} (Algo2Lean.UnionFind.potential state)
                      (Algo2Lean.Ackermann.alpha n)) :=
  Algo2Lean.UnionFind.link_potential
