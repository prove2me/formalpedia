-- Prove2me | solution 1 for Algo2Lean.UnionFind.compress_valid
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-10T23:53:36.264261+00:00
-- url     : https://prove2.me/submissions/b1f1f113-5965-4713-9e3e-10836888fe5e

import Definitions.Def_Algo2LeanLib_UnionFind


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

theorem rank_lt_representative {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) (moving : state.parent vertex ≠ vertex) :
    state.rank vertex < state.rank (state.representative vertex) := by
  have rising := valid.parent_rank vertex moving
  have bounded := rank_le_representative valid (state.parent vertex)
  rw [valid.parent_representative vertex] at bounded
  omega







theorem compress_root_iff {n : Nat} {state : State n} (valid : Valid state)
    (vertex other : Fin n) :
    (compress state vertex).parent other = other ↔ state.parent other = other := by
  by_cases same : other = vertex
  · subst other
    simp only [compress, update_same]
    constructor
    · intro fixed
      have := valid.representative_root vertex
      simpa [fixed] using this
    · exact valid.root_representative vertex
  · simp [compress, update, same]

/-- A path-compression write preserves all forest and mass invariants. -/
theorem compress_valid {n : Nat} {state : State n} (valid : Valid state)
    (vertex : Fin n) : Valid (compress state vertex) := by
  constructor
  · intro other
    exact (compress_root_iff valid vertex _).mpr (valid.representative_root other)
  · intro other fixed
    exact valid.root_representative other ((compress_root_iff valid vertex other).mp fixed)
  · intro other
    by_cases same : other = vertex
    · subst other
      simp only [compress, update_same]
      exact valid.root_representative _ (valid.representative_root vertex)
    · simpa [compress, update, same] using valid.parent_representative other
  · intro other moving
    have oldMoving : state.parent other ≠ other := fun fixed =>
      moving ((compress_root_iff valid vertex other).mpr fixed)
    by_cases same : other = vertex
    · subst other
      simpa [compress] using rank_lt_representative valid vertex oldMoving
    · simpa [compress, update, same] using valid.parent_rank other oldMoving
  · intro other fixed
    exact valid.root_mass other ((compress_root_iff valid vertex other).mp fixed)
  · intro other moving
    exact valid.nonroot_mass other (fun fixed => moving ((compress_root_iff valid vertex other).mpr fixed))
  · exact valid.mass_budget



























end Algo2Lean.UnionFind

end

set_option autoImplicit false
theorem solution :
    ∀ {n : Nat} {state : Algo2Lean.UnionFind.State n},
      Algo2Lean.UnionFind.Valid state →
        ∀ (vertex : Fin n), Algo2Lean.UnionFind.Valid (Algo2Lean.UnionFind.compress state vertex) :=
  Algo2Lean.UnionFind.compress_valid
