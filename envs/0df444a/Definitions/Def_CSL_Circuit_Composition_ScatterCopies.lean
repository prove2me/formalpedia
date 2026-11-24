-- Prove2me | Definitions.Def_CSL_Circuit_Composition_ScatterCopies
-- name    : CSL_Circuit_Composition_ScatterCopies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:11:47.799393+00:00
-- url     : https://prove2.me/theorems/106d7f0f-d5d2-469f-88b6-e8314867bd56
-- title:
--   Coded sorting library: Circuit / Composition / ScatterCopies
-- statement:
--   Module `CodedSorting.Circuit.Composition.ScatterCopies` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Temporary copies in the XOR instruction sequence. The reduced program reads the original helper registers. The expanded program copies their values into temporary registers before distributing them. The programs agree on the original registers for every initial temporary value.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Composition.ScatterCopies

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_NetworkModel_NetworkAdapter
import Definitions.Def_CSL_Circuit_Local_FiniteSemantics
import Mathlib.Logic.Equiv.Fin.Basic

section ExplicitCopies
/-! Temporary copies in the XOR instruction sequence. The reduced program reads the original helper registers. The expanded program copies their values into temporary registers before distributing them. The programs agree on the original registers for every initial temporary value. 








-/

set_option autoImplicit false

namespace CSL.Construction.ExplicitCopies

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.NetworkAdapter
open scoped BigOperators

variable {R T : Type*} [DecidableEq R] [DecidableEq T]

/-- The original registers and the temporary registers are disjoint. -/
def originalEmbedding : R ↪ R ⊕ T := ⟨Sum.inl, Sum.inl_injective⟩

def temporaryEmbedding : T ↪ R ⊕ T := ⟨Sum.inr, Sum.inr_injective⟩

/-- Restriction to the original registers. -/
def originalState (state : R ⊕ T → Bit) : R → Bit := state ∘ Sum.inl

/-- An actual existing `XorGate` overwrites a temporary register, including
when its old value is nonzero. -/
def copyGate (helper : T → R) (t : T) : XorGate (R ⊕ T) :=
  overwriteCopy (.inr t) (.inl (helper t))

def copyProgram (helper : T → R) (temporaries : List T) : List (XorGate (R ⊕ T)) :=
  temporaries.map (copyGate helper)

@[simp] theorem copyGate_original (helper : T → R) (t : T)
    (state : R ⊕ T → Bit) (r : R) :
    (copyGate helper t).eval state (.inl r) = state (.inl r) := by
  exact overwriteCopy_away _ _ _ _ (by simp)

@[simp] theorem copyGate_temporary (helper : T → R) (t u : T)
    (state : R ⊕ T → Bit) :
    (copyGate helper t).eval state (.inr u) =
      if u = t then state (.inl (helper t)) else state (.inr u) := by
  by_cases h : u = t
  · subst u
    first
    | exact overwriteCopy_at_destination (Sum.inr t) (Sum.inl (helper t)) (by simp) state
    | (have h_sx := overwriteCopy_at_destination (Sum.inr t) (Sum.inl (helper t)) (by simp) state; simp  at h_sx ⊢; exact h_sx)
    | (have h_sx := overwriteCopy_at_destination (Sum.inr t) (Sum.inl (helper t)) (by simp) state; simp  at h_sx; exact h_sx)
    | (simp ; exact overwriteCopy_at_destination (Sum.inr t) (Sum.inl (helper t)) (by simp) state)
  · rw [if_neg h]
    exact overwriteCopy_away _ _ _ _ (by simpa using h)

/-- Copying introduces no change to any original register. -/
theorem copyProgram_original (helper : T → R) (temporaries : List T)
    (state : R ⊕ T → Bit) :
    originalState (runProgram (copyProgram helper temporaries) state) =
      originalState state := by
  induction temporaries generalizing state with
  | nil => rfl
  | cons t ts ih =>
    simp only [copyProgram, List.map_cons, runProgram] at *
    rw [ih]
    funext r
    exact copyGate_original helper t state r

/-- Every copied temporary contains its helper value from before the copy
batch. Repeated copies are harmless, and no zero-initialization is assumed. -/
theorem copyProgram_temporary (helper : T → R) (temporaries : List T)
    (state : R ⊕ T → Bit) (t : T) :
    runProgram (copyProgram helper temporaries) state (.inr t) =
      if t ∈ temporaries then state (.inl (helper t)) else state (.inr t) := by
  induction temporaries generalizing state with
  | nil => simp [copyProgram, runProgram]
  | cons u us ih =>
    simp only [copyProgram, List.map_cons, runProgram] at *
    rw [ih]
    by_cases hmem : t ∈ us
    · simp [hmem]
    · by_cases heq : t = u
      · subst u
        simp [hmem]
      · simp [hmem, heq]

/-- Coherence is the invariant needed while scatter reads the frozen copies. -/
def CopiesAgree (helper : T → R) (state : R ⊕ T → Bit) : Prop :=
  ∀ t, state (.inr t) = state (.inl (helper t))

theorem copyProgram_agree (helper : T → R) (temporaries : List T)
    (hcomplete : ∀ t, t ∈ temporaries) (state : R ⊕ T → Bit) :
    CopiesAgree helper (runProgram (copyProgram helper temporaries) state) := by
  intro t
  rw [copyProgram_temporary, if_pos (hcomplete t)]
  exact (congrFun (copyProgram_original helper temporaries state) (helper t)).symm

/-- Once all temporaries have been overwritten, their previous contents
have no influence on the entire state, not just its original projection. -/
theorem copyProgram_independent_of_dirty (helper : T → R) (temporaries : List T)
    (hcomplete : ∀ t, t ∈ temporaries) (left right : R ⊕ T → Bit)
    (hsame : originalState left = originalState right) :
    runProgram (copyProgram helper temporaries) left =
      runProgram (copyProgram helper temporaries) right := by
  funext r
  cases r with
  | inl r =>
    exact congrFun ((copyProgram_original helper temporaries left).trans
      (hsame.trans (copyProgram_original helper temporaries right).symm)) r
  | inr t =>
    rw [copyProgram_temporary, copyProgram_temporary,
      if_pos (hcomplete t), if_pos (hcomplete t)]
    exact congrFun hsame (helper t)

end CSL.Construction.ExplicitCopies
end ExplicitCopies

section ScatterCopies
/-! Removing temporary scatter copies. The expanded program runs the preceding instructions, copies each retained helper into its temporary register, distributes those temporary values, and runs the following instructions. The reduced program reads the retained helpers directly. Their outputs on the original registers agree when scatter preserves the retained helpers. 










-/

set_option autoImplicit false

namespace CSL.Construction.ScatterCopies

open CSL.Circuit CSL.CircuitProgram
open CSL.Construction.ExplicitCopies
open scoped BigOperators

variable {R T : Type*} [DecidableEq R] [DecidableEq T]

/-- A scatter row names its original destination and the retained helpers
whose copied values are added to that destination. -/
structure ScatterRow (R T : Type*) where
  destination : R
  sources : Finset T

def originalScatter (helper : T ↪ R) (row : ScatterRow R T) : XorGate R where
  ports := {row.destination} ∪ row.sources.map helper
  targets := {row.destination}
  controls _ := row.sources.map helper
  targets_subset := Finset.subset_union_left
  controls_subset := by intro _ _; exact Finset.subset_union_right

def copiedScatter (row : ScatterRow R T) : XorGate (R ⊕ T) where
  ports := {Sum.inl row.destination} ∪ row.sources.map temporaryEmbedding
  targets := {Sum.inl row.destination}
  controls _ := row.sources.map temporaryEmbedding
  targets_subset := Finset.subset_union_left
  controls_subset := by intro _ _; exact Finset.subset_union_right

theorem originalScatter_eval (helper : T ↪ R) (row : ScatterRow R T)
    (state : R → Bit) (r : R) :
    (originalScatter helper row).eval state r =
      if r = row.destination then state r + ∑ t ∈ row.sources, state (helper t)
      else state r := by
  simp [originalScatter, XorGate.eval, Finset.sum_map]

theorem copiedScatter_original (row : ScatterRow R T)
    (state : R ⊕ T → Bit) (r : R) :
    (copiedScatter row).eval state (.inl r) =
      if r = row.destination then state (.inl r) + ∑ t ∈ row.sources, state (.inr t)
      else state (.inl r) := by
  simp [copiedScatter, XorGate.eval, Finset.sum_map, temporaryEmbedding]

@[simp] theorem copiedScatter_temporary (row : ScatterRow R T)
    (state : R ⊕ T → Bit) (t : T) :
    (copiedScatter row).eval state (.inr t) = state (.inr t) := by
  simp [copiedScatter, XorGate.eval]

/-- Frozen copies give the same scatter output on all original registers. -/
theorem copiedScatter_eq_original (helper : T ↪ R) (row : ScatterRow R T)
    (state : R ⊕ T → Bit) (hcopies : CopiesAgree helper state) :
    originalState ((copiedScatter row).eval state) =
      (originalScatter helper row).eval (originalState state) := by
  funext r
  change (copiedScatter row).eval state (.inl r) = _
  rw [copiedScatter_original, originalScatter_eval]
  change ∀ t, state (.inr t) = state (.inl (helper t)) at hcopies
  simp only [originalState, Function.comp_apply, hcopies]

/-- Copy coherence survives a scatter row when its destination is not a
retained helper. The temporary registers themselves are never targets. -/
theorem copiedScatter_agree (helper : T ↪ R) (row : ScatterRow R T)
    (hsafe : ∀ t, helper t ≠ row.destination)
    (state : R ⊕ T → Bit) (hcopies : CopiesAgree helper state) :
    CopiesAgree helper ((copiedScatter row).eval state) := by
  intro t
  rw [copiedScatter_temporary, copiedScatter_original, if_neg (hsafe t)]
  exact hcopies t

def reducedScatter (helper : T ↪ R) (rows : List (ScatterRow R T)) :
    List (XorGate R) := rows.map (originalScatter helper)

def physicalScatter (rows : List (ScatterRow R T)) :
    List (XorGate (R ⊕ T)) := rows.map copiedScatter

theorem physicalScatter_agree (helper : T ↪ R) (rows : List (ScatterRow R T))
    (hsafe : ∀ row ∈ rows, ∀ t, helper t ≠ row.destination)
    (state : R ⊕ T → Bit) (hcopies : CopiesAgree helper state) :
    CopiesAgree helper (runProgram (physicalScatter rows) state) := by
  induction rows generalizing state with
  | nil => exact hcopies
  | cons row rows ih =>
    apply ih (fun r hr => hsafe r (List.mem_cons_of_mem row hr))
    exact copiedScatter_agree helper row (hsafe row (by simp)) state hcopies

theorem physicalScatter_original (helper : T ↪ R) (rows : List (ScatterRow R T))
    (hsafe : ∀ row ∈ rows, ∀ t, helper t ≠ row.destination)
    (state : R ⊕ T → Bit) (hcopies : CopiesAgree helper state) :
    originalState (runProgram (physicalScatter rows) state) =
      runProgram (reducedScatter helper rows) (originalState state) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih =>
    simp only [physicalScatter, reducedScatter, List.map_cons, runProgram] at *
    rw [ih (fun r hr => hsafe r (List.mem_cons_of_mem row hr))
      ((copiedScatter row).eval state)
      (copiedScatter_agree helper row (hsafe row (by simp)) state hcopies)]
    rw [copiedScatter_eq_original helper row state hcopies]

variable [Fintype R]

noncomputable def expandedProgram (helper : T ↪ R) (temporaries : List T)
    (before after : List (XorGate R)) (rows : List (ScatterRow R T)) :
    List (XorGate (R ⊕ T)) :=
  before.map (XorGate.lift originalEmbedding) ++ copyProgram helper temporaries ++
    physicalScatter rows ++ after.map (XorGate.lift originalEmbedding)

def reducedProgram (helper : T ↪ R) (before after : List (XorGate R))
    (rows : List (ScatterRow R T)) : List (XorGate R) :=
  before ++ reducedScatter helper rows ++ after

theorem liftProgram_original (program : List (XorGate R)) (state : R ⊕ T → Bit) :
    originalState (runProgram (program.map (XorGate.lift originalEmbedding)) state) =
      runProgram program (originalState state) :=
  runProgram_lift_restrict originalEmbedding program state

/-- Erasing the explicit copies and redirecting scatter back to the helpers
preserves the entire original-register output. There are no assumptions on
the initial temporary values, the before, or the after. -/
theorem expandedProgram_original (helper : T ↪ R) (temporaries : List T)
    (hcomplete : ∀ t, t ∈ temporaries)
    (before after : List (XorGate R)) (rows : List (ScatterRow R T))
    (hsafe : ∀ row ∈ rows, ∀ t, helper t ≠ row.destination)
    (state : R ⊕ T → Bit) :
    originalState (runProgram (expandedProgram helper temporaries before after rows) state) =
      runProgram (reducedProgram helper before after rows) (originalState state) := by
  simp only [expandedProgram, reducedProgram, runProgram_append, liftProgram_original]
  rw [physicalScatter_original helper rows hsafe _
    (copyProgram_agree helper temporaries hcomplete _)]
  rw [copyProgram_original, liftProgram_original]

/-- Two executions with identical original inputs have identical original
outputs even when every temporary input is changed. -/
theorem expandedProgram_independent_of_dirty (helper : T ↪ R) (temporaries : List T)
    (hcomplete : ∀ t, t ∈ temporaries)
    (before after : List (XorGate R)) (rows : List (ScatterRow R T))
    (hsafe : ∀ row ∈ rows, ∀ t, helper t ≠ row.destination)
    (left right : R ⊕ T → Bit) (hsame : originalState left = originalState right) :
    originalState (runProgram (expandedProgram helper temporaries before after rows) left) =
      originalState (runProgram (expandedProgram helper temporaries before after rows) right) := by
  rw [expandedProgram_original helper temporaries hcomplete before after rows hsafe,
    expandedProgram_original helper temporaries hcomplete before after rows hsafe, hsame]

end CSL.Construction.ScatterCopies
end ScatterCopies


