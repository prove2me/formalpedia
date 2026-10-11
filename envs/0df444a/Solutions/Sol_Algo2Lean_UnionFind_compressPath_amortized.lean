-- Prove2me | solution 1 for Algo2Lean.UnionFind.compressPath_amortized
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:54:57.026681+00:00
-- url     : https://prove2.me/submissions/34d61443-34f9-41ac-b981-f4775d5ed112

import Definitions.Def_Algo2LeanLib_UnionFindAmortized


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



/-- Every stored rank is bounded by the fixed universe size. -/
theorem rank_le_size {n : Nat} {state : State n} (valid : Valid state) (vertex : Fin n) :
    state.rank vertex ≤ n :=
  Nat.le_trans (rank_le_representative valid vertex)
    (Nat.le_trans (root_rank_le_log valid _ (valid.representative_root vertex)) (Nat.log2_le_self n))

/-- Compression of higher-ranked vertices leaves a lower-ranked vertex untouched. -/
theorem compressPath_parent_below {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps)
    (other : Fin n) (lower : state.rank other < state.rank vertex) :
    (compressPath state vertex steps).parent other = state.parent other := by
  induction path with
  | root vertex fixed => rfl
  | step vertex root steps moving tail ih =>
    have nextLower : state.rank other < state.rank (state.parent vertex) :=
      Nat.lt_trans lower (valid.parent_rank vertex moving)
    have different : other ≠ vertex := by intro same; subst other; omega
    simpa [compressPath, compress, update, different] using ih nextLower

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

theorem iterations_pos {size rank parentRank : Nat} (rising : rank < parentRank) :
    0 < iterations size rank parentRank := by
  have first := level_spec (size := size) rising
  have success := le_boundedMax
    (fun count => decide (iterate (ack (level size rank parentRank)) count rank ≤ parentRank))
    (rank + 1) 1 (by omega) (by simpa using first)
  change 1 ≤ iterations size rank parentRank at success
  omega

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



theorem progress_le {size rank parentRank : Nat} (positive : 0 < rank)
    (rising : rank < parentRank) (bounded : parentRank ≤ size) :
    progress size rank parentRank ≤ alpha size * rank := by
  have levels := level_lt_alpha positive rising bounded
  have counts := iterations_le_rank positive rising bounded
  have product := Nat.mul_le_mul_right rank (show level size rank parentRank + 1 ≤ alpha size by omega)
  simp only [Nat.add_mul, Nat.one_mul] at product
  unfold progress
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

theorem progress_strict {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size)
    (advanced : iterate (ack (level size rank before)) (iterations size rank before + 1) rank ≤ after) :
    progress size rank before < progress size rank after := by
  have levels := level_mono (size := size) rising grows
  by_cases same : level size rank before = level size rank after
  · have within := iterations_le_rank positive rising (by omega : before ≤ size)
    have counts := le_boundedMax
      (fun count => decide (iterate (ack (level size rank after)) count rank ≤ after))
      (rank + 1) (iterations size rank before + 1) (by omega) (by simpa [same] using advanced)
    change iterations size rank before + 1 ≤ iterations size rank after at counts
    simp only [progress, same]
    omega
  · have counts := iterations_le_rank positive rising (by omega : before ≤ size)
    have positiveCount := iterations_pos (size := size) (by omega : rank < after)
    have product := Nat.mul_le_mul_right rank
      (show level size rank before + 1 ≤ level size rank after by omega)
    simp only [Nat.add_mul, Nat.one_mul] at product
    unfold progress
    omega









theorem credit_mono {size rank before after : Nat} (rising : rank < before)
    (grows : before ≤ after) (bounded : after ≤ size) : credit size rank after ≤ credit size rank before := by
  by_cases zero : rank = 0
  · simp [zero]
  · have progress := progress_mono (by omega : 0 < rank) rising grows bounded
    simp only [credit, zero, false_or, if_neg (show ¬ before ≤ rank by omega),
      if_neg (show ¬ after ≤ rank by omega)]
    omega

theorem credit_strict {size rank before after : Nat} (positive : 0 < rank)
    (rising : rank < before) (grows : before ≤ after) (bounded : after ≤ size)
    (advanced : iterate (ack (level size rank before)) (iterations size rank before + 1) rank ≤ after) :
    credit size rank after + 1 ≤ credit size rank before := by
  have progressRises := progress_strict positive rising grows bounded advanced
  have progressBound := progress_le positive (by omega : rank < after) bounded
  simp only [credit, show ¬ rank = 0 by omega, false_or,
    if_neg (show ¬ before ≤ rank by omega), if_neg (show ¬ after ≤ rank by omega)]
  omega





/-- One compression write changes only the credit at the written vertex. -/
theorem compress_potential_balance {n : Nat} (state : State n) (vertex : Fin n) :
    potential (compress state vertex) + credit n (state.rank vertex) (state.rank (state.parent vertex)) =
      potential state + credit n (state.rank vertex) (state.rank (state.representative vertex)) := by
  have entries : (fun other => credit n ((compress state vertex).rank other)
      ((compress state vertex).rank ((compress state vertex).parent other))) =
      update (fun other => credit n (state.rank other) (state.rank (state.parent other))) vertex
        (credit n (state.rank vertex) (state.rank (state.representative vertex))) := by
    funext other
    by_cases same : other = vertex <;> simp [compress, update, same]
  unfold potential
  rw [entries]
  exact total_update _ vertex _



/-- During recursive return, the tail's compression has not changed this vertex's old parent. -/
theorem compressPath_potential_balance {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (moving : state.parent vertex ≠ vertex)
    (tail : Find state (state.parent vertex) root steps) :
    potential (compressPath state vertex (steps + 1)) +
        credit n (state.rank vertex) (state.rank (state.parent vertex)) =
      potential (compressPath state (state.parent vertex) steps) +
        credit n (state.rank vertex) (state.rank root) := by
  have balance := compress_potential_balance (compressPath state (state.parent vertex) steps) vertex
  have unchanged := compressPath_parent_below valid tail vertex (valid.parent_rank vertex moving)
  have rootCorrect := (find_correct valid (Find.step vertex root steps moving tail)).1
  simpa only [compressPath, compressPath_rank, compressPath_representative, unchanged, ← rootCorrect] using balance







theorem levelCount_le (size : Nat) (levels : List Nat) : levelCount size levels ≤ alpha size := by
  have bounded : levelCount size levels ≤ total (n := alpha size) (fun _ => 1) := by
    apply total_mono
    intro index
    split <;> omega
  simpa [total_ones] using bounded



theorem levelCount_cons_present (size level : Nat) (levels : List Nat) (present : level ∈ levels) :
    levelCount size (level :: levels) = levelCount size levels := by
  unfold levelCount
  congr 1
  funext index
  by_cases same : index.val = level
  · simp [List.mem_cons, same, present]
  · simp [List.mem_cons, same]

theorem levelCount_cons_fresh (size level : Nat) (levels : List Nat)
    (within : level < alpha size) (fresh : level ∉ levels) :
    levelCount size (level :: levels) = levelCount size levels + 1 := by
  let index : Fin (alpha size) := ⟨level, within⟩
  have entries : (fun other : Fin (alpha size) => if other.val ∈ level :: levels then 1 else 0) =
      update (fun other : Fin (alpha size) => if other.val ∈ levels then 1 else 0) index 1 := by
    funext other
    by_cases same : other = index
    · subst other
      simp [index, update]
    · have different : other.val ≠ level := by
        intro equal
        exact same (Fin.ext equal)
      simp [List.mem_cons, update, same, different]
  unfold levelCount
  rw [entries]
  have replacement := total_update (fun other : Fin (alpha size) => if other.val ∈ levels then 1 else 0) index 1
  simpa [index, fresh] using replacement



/-- A listed path level has a positive-rank witness between the start and the root. -/
theorem pathLevels_member {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps key : Nat} (path : Find state vertex root steps)
    (member : key ∈ pathLevels state vertex steps) :
    ∃ rank parentRank, 0 < rank ∧ rank < parentRank ∧ state.rank vertex ≤ rank ∧
      parentRank ≤ state.rank root ∧ level n rank parentRank = key := by
  induction path with
  | root vertex fixed => simp [pathLevels] at member
  | step vertex root steps moving tail ih =>
    have rising := valid.parent_rank vertex moving
    have upper := (find_correct valid tail).2.2
    simp only [pathLevels] at member
    split at member
    · obtain ⟨rank, parentRank, positive, increasing, lower, upper, same⟩ := ih member
      exact ⟨rank, parentRank, positive, increasing, by omega, upper, same⟩
    · rename_i positive
      rcases List.mem_cons.mp member with same | later
      · exact ⟨_, _, by omega, rising, Nat.le_refl _, by omega, same.symm⟩
      · obtain ⟨rank, parentRank, positive, increasing, lower, upper, same⟩ := ih later
        exact ⟨rank, parentRank, positive, increasing, by omega, upper, same⟩

/-- A repeated old level forces one additional iteration after both nodes point to the root. -/
theorem repeated_level_advance {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (moving : state.parent vertex ≠ vertex)
    (tail : Find state (state.parent vertex) root steps)
    (repeated : level n (state.rank vertex) (state.rank (state.parent vertex)) ∈
      pathLevels state (state.parent vertex) steps) :
    iterate (ack (level n (state.rank vertex) (state.rank (state.parent vertex))))
      (iterations n (state.rank vertex) (state.rank (state.parent vertex)) + 1)
      (state.rank vertex) ≤ state.rank root := by
  obtain ⟨rank, parentRank, positive, increasing, lower, upper, sameLevel⟩ :=
    pathLevels_member valid tail repeated
  have first := iterations_spec (size := n) (valid.parent_rank vertex moving)
  have second := level_spec (size := n) increasing
  rw [sameLevel] at second
  rw [iterate_succ]
  exact Nat.le_trans (ack_mono_right _ (Nat.le_trans first lower)) (Nat.le_trans second upper)

/-- All path steps are paid by lost credit except a rank-zero first node and
    the last occurrence of each old Ackermann level. -/
theorem compressPath_amortized_aux {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    steps + potential (compressPath state vertex steps) ≤ potential state +
      levelCount n (pathLevels state vertex steps) + if state.rank vertex = 0 then 1 else 0 := by
  induction path with
  | root vertex fixed => simp [compressPath, pathLevels]
  | step vertex root steps moving tail ih =>
    have rising := valid.parent_rank vertex moving
    have upper := (find_correct valid tail).2.2
    have bounded := rank_le_size valid root
    have balance := compressPath_potential_balance valid moving tail
    have parentPositive : state.rank (state.parent vertex) ≠ 0 := by omega
    simp only [parentPositive, ↓reduceIte, Nat.add_zero] at ih
    by_cases zero : state.rank vertex = 0
    · simp only [zero, credit_zero] at balance
      simp only [pathLevels, zero, ↓reduceIte]
      omega
    · have smaller := credit_mono rising (by omega : state.rank (state.parent vertex) ≤ state.rank root) bounded
      by_cases repeated : level n (state.rank vertex) (state.rank (state.parent vertex)) ∈
          pathLevels state (state.parent vertex) steps
      · have strict := credit_strict (by omega : 0 < state.rank vertex) rising
          (by omega : state.rank (state.parent vertex) ≤ state.rank root) bounded
          (repeated_level_advance valid moving tail repeated)
        simp only [pathLevels, zero, ↓reduceIte, levelCount_cons_present _ _ _ repeated, Nat.add_zero]
        omega
      · have within := level_lt_alpha (by omega : 0 < state.rank vertex) rising
          (rank_le_size valid (state.parent vertex))
        simp only [pathLevels, zero, ↓reduceIte, levelCount_cons_fresh _ _ _ within repeated, Nat.add_zero]
        omega

/-- The pure inverse-Ackermann amortized path-compression bound. -/
theorem compressPath_amortized {n : Nat} {state : State n} (valid : Valid state)
    {vertex root : Fin n} {steps : Nat} (path : Find state vertex root steps) :
    steps + potential (compressPath state vertex steps) ≤ potential state + alpha n + 1 := by
  have charged := compressPath_amortized_aux valid path
  have levels := levelCount_le n (pathLevels state vertex steps)
  split at charged <;> omega









-- Main result: Running time




end
end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ {vertex root : Fin n} {steps : Nat},
          Algo2Lean.UnionFind.Find state vertex root steps →
            LE.le.{0}
              (HAdd.hAdd.{0, 0, 0} steps
                (Algo2Lean.UnionFind.potential (Algo2Lean.UnionFind.compressPath state vertex steps)))
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0} (Algo2Lean.UnionFind.potential state)
                  (Algo2Lean.Ackermann.alpha n))
                (1 : Nat)) :=
  Algo2Lean.UnionFind.compressPath_amortized
