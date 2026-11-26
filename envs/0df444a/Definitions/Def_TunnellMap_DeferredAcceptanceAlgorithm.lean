-- Prove2me | Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
-- name    : TunnellMap_DeferredAcceptanceAlgorithm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:05:04.244558+00:00
-- url     : https://prove2.me/theorems/c3cb7bef-39e2-4b0b-9168-1264b0fe7c50
-- title:
--   Deferred Acceptance Algorithm
-- statement:
--   Definitions and structural lemmas for Deferred Acceptance Algorithm, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAlgorithm.lean

import Definitions.Def_TunnellMap_DeferredAcceptance
import Definitions.Def_TunnellMap_PreferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList


set_option autoImplicit true
namespace TunnellMap
namespace GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
structure DAState (I : GloballyRanked K S T) where
  queue : List S
  cursor : S → ℕ
  held : T → Option S
  assigned : S → Option T
  cursor_le : ∀ s, cursor s ≤ Fintype.card T
namespace DAState
variable (I : GloballyRanked K S T)
def initial (sourceOrder : List S) : I.DAState where
  queue := sourceOrder
  cursor := fun _ => 0
  held := fun _ => none
  assigned := fun _ => none
  cursor_le := by simp
noncomputable def nextTarget (st : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T) : T :=
  (I.preferenceList s).get
    ⟨st.cursor s, by simpa using h⟩
def advancedCursor (st : I.DAState) (s : S) : S → ℕ :=
  Function.update st.cursor s (st.cursor s + 1)
theorem advancedCursor_le (st : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T) :
    ∀ x, st.advancedCursor I s x ≤ Fintype.card T := by
  intro x
  by_cases hx : x = s
  · subst x
    simp [advancedCursor]
    omega
  · simpa [advancedCursor, hx] using st.cursor_le x
noncomputable def acceptEmpty (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) : I.DAState :=
  let t := st.nextTarget I s h
  { queue := rest
    cursor := st.advancedCursor I s
    held := Function.update st.held t (some s)
    assigned := Function.update st.assigned s (some t)
    cursor_le := st.advancedCursor_le I s h }
noncomputable def replaceHeld (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) (old : S) : I.DAState :=
  let t := st.nextTarget I s h
  { queue := rest ++ [old]
    cursor := st.advancedCursor I s
    held := Function.update st.held t (some s)
    assigned := Function.update
      (Function.update st.assigned old none) s (some t)
    cursor_le := st.advancedCursor_le I s h }
noncomputable def rejectProposal (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) : I.DAState :=
  { queue := rest ++ [s]
    cursor := st.advancedCursor I s
    held := st.held
    assigned := st.assigned
    cursor_le := st.advancedCursor_le I s h }
noncomputable def advance (st : I.DAState) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) : I.DAState :=
  let t := st.nextTarget I s h
  match ht : st.held t with
  | none => st.acceptEmpty I s rest h
  | some old =>
      if hbetter : I.rank s t < I.rank old t then
        st.replaceHeld I s rest h old
      else
        st.rejectProposal I s rest h
noncomputable def step (st : I.DAState) : Option I.DAState :=
  match st.queue with
  | [] => none
  | s :: rest =>
      if h : st.cursor s < Fintype.card T then
        some (st.advance I s rest h)
      else
        none
@[simp] theorem advance_cursor_self (st : I.DAState) (s : S)
    (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).cursor s = st.cursor s + 1 := by
  simp only [advance]
  split
  · simp [acceptEmpty, advancedCursor]
  · split <;> simp [replaceHeld, rejectProposal, advancedCursor]
@[simp] theorem advance_cursor_of_ne (st : I.DAState) (s x : S)
    (rest : List S) (h : st.cursor s < Fintype.card T) (hx : x ≠ s) :
    (st.advance I s rest h).cursor x = st.cursor x := by
  simp only [advance]
  split
  · simp [acceptEmpty, advancedCursor, hx]
  · split <;> simp [replaceHeld, rejectProposal, advancedCursor, hx]
def remaining (st : I.DAState) : ℕ :=
  (Finset.univ : Finset S).sum fun s => Fintype.card T - st.cursor s
theorem remaining_advance_add_one (st : I.DAState) (s : S)
    (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).remaining I + 1 = st.remaining I := by
  classical
  let m := Fintype.card T
  let f : S → ℕ := fun x => m - st.cursor x
  let f' : S → ℕ := fun x => m - (st.advance I s rest h).cursor x
  have hf' : f' = Function.update f s (m - (st.cursor s + 1)) := by
    funext x
    by_cases hx : x = s
    · subst x
      simp [f, f']
    · simp [f, f', hx]
  have hsplit :
      f s + ∑ x ∈ (Finset.univ : Finset S).erase s, f x =
        ∑ x : S, f x :=
    Finset.add_sum_erase (Finset.univ : Finset S) f (Finset.mem_univ s)
  unfold remaining
  change (∑ x : S, f' x) + 1 = ∑ x : S, f x
  rw [hf', Finset.sum_update_of_mem (Finset.mem_univ s)]
  rw [Finset.sdiff_singleton_eq_erase]
  calc
    (m - (st.cursor s + 1) +
        ∑ x ∈ (Finset.univ : Finset S).erase s, f x) + 1 =
        (m - st.cursor s) +
          ∑ x ∈ (Finset.univ : Finset S).erase s, f x := by omega
    _ = ∑ x : S, f x := hsplit
theorem remaining_advance_lt (st : I.DAState) (s : S)
    (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).remaining I < st.remaining I := by
  have := remaining_advance_add_one I st s rest h
  omega
theorem remaining_step_lt (st st' : I.DAState)
    (hstep : st.step I = some st') :
    st'.remaining I < st.remaining I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact remaining_advance_lt I st s rest hcur
      · simp [step, hqueue, hcur] at hstep
noncomputable def run (st : I.DAState) : I.DAState :=
  match hstep : st.step I with
  | none => st
  | some st' => run st'
termination_by st.remaining I
decreasing_by exact remaining_step_lt I st st' hstep
end DAState
end GloballyRanked
end TunnellMap


