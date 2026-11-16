-- Prove2me | solution 1 for APFPaper1.RecordOccupant.side_is_the_allowed_states
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:26:54.468932+00:00
-- url     : https://prove2.me/submissions/74e5bf12-84f0-4138-97f1-7812a8e88150

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_records_at_a_potential_state
title: A side the kept records give is the side of every potential state they allow; of the two records of a distinction's sides exactly one is true of a given potential state; and once one is kept, keeping the other allows no state
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper1_RecordOccupant (this seat). Codebank apf/plec.py: check_Regime_exit_Type_III (record
 locking as a change of admissible class).
scope_after_the_ruling: the author ruled on 2026-11-14 18:57 HST that where nothing is recorded the occupant
 itself has no side (RULING_occupant_forms_2026-11-14). A potential state has a side on every distinction,
 so the state x below is NOT the occupant in raw form. This file was first written (bundle v18, as
 Thm_APFPaper1_records_at_an_occupant) on this seat's misreading that the occupant is such a point; that
 file is superseded by this one, with the same proofs and corrected names and wording. Four theorems here
 are statements about any one potential state the records allow. other_side_never_after mentions no such
 state: it says that a side in record form is not reversed while its record is kept.
consumes_inputs: none. Ordinary mathematics on the definitions.
named_hypotheses: x in allowed allows K (the kept records allow the potential state x). In the theorems
 about side records, hr (a record allows exactly the potential states on one side of d).
statement: (side_is_the_allowed_states) if the kept records allow x and have side b on d, x reads d as b.
 (exactly_one_side_record_true) of the record of side true and the record of side false, exactly one allows
 x. (gains_the_allowed_states_side) keeping the record of x's side of d still allows x and gives the
 records that side on d. (no_tie_at_a_potential_state) the two ways of gaining a side on d never both
 allow x. (other_side_never_after) once a record of one side is kept, keeping a record of the other side
 allows no potential state.
not_claimed: that the occupant is a potential state (ruled otherwise); that anything picks the side an
 occupant in raw form gains: see Thm_APFPaper1_RecordOccupant_gaining_a_side. No lane. No claim that the
 transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
-/
import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-- If the kept records allow `x` and have side `b` on `d`, then `x` reads `d` as `b`. -/
theorem side_is_the_allowed_states (reads : D → X → Bool) (allows : Rec → X → Prop)
    (K : Finset Rec) (x : X) (hx : x ∈ allowed allows K) (d : D) (b : Bool)
    (h : HasSide reads allows K d b) : reads d x = b :=
  h.2 x hx

/-- Of the record of side true and the record of side false, exactly one allows `x`. -/
theorem exactly_one_side_record_true (reads : D → X → Bool) (allows : Rec → X → Prop) (d : D)
    (rt rf : Rec) (hrt : ∀ y, allows rt y ↔ reads d y = true)
    (hrf : ∀ y, allows rf y ↔ reads d y = false) (x : X) :
    (allows rt x ∧ ¬ allows rf x) ∨ (allows rf x ∧ ¬ allows rt x) := by
  cases h : reads d x
  · refine Or.inr ⟨(hrf x).mpr h, fun h' => ?_⟩
    have h2 := (hrt x).mp h'
    rw [h] at h2
    exact absurd h2 (by decide)
  · refine Or.inl ⟨(hrt x).mpr h, fun h' => ?_⟩
    have h2 := (hrf x).mp h'
    rw [h] at h2
    exact absurd h2 (by decide)

/-- Keeping the record of `x`'s side of `d` still allows `x` and gives the records that side on
`d`. -/
theorem gains_the_allowed_states_side [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (x : X) (hx : x ∈ allowed allows K) (d : D)
    (r : Rec) (hr : ∀ y, allows r y ↔ reads d y = reads d x) :
    x ∈ allowed allows (insert r K) ∧ HasSide reads allows (insert r K) d (reads d x) := by
  have hx' : x ∈ allowed allows (insert r K) := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact (hr x).mpr rfl
    · exact hx s hs'
  exact ⟨hx', ⟨x, hx'⟩, fun y hy => (hr y).mp (hy r (Finset.mem_insert_self r K))⟩

/-- The two ways of gaining a side on `d` never both allow `x`. -/
theorem no_tie_at_a_potential_state [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (x : X) (d : D) (rt rf : Rec)
    (hrt : ∀ y, allows rt y ↔ reads d y = true) (hrf : ∀ y, allows rf y ↔ reads d y = false) :
    ¬ (x ∈ allowed allows (insert rt K) ∧ x ∈ allowed allows (insert rf K)) := by
  rintro ⟨h1, h2⟩
  have a := (hrt x).mp (h1 rt (Finset.mem_insert_self rt K))
  have b := (hrf x).mp (h2 rf (Finset.mem_insert_self rf K))
  rw [a] at b
  exact absurd b (by decide)

/-- Once a record of one side is kept, keeping a record of the other side allows no potential
state. -/
theorem other_side_never_after [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (b : Bool) (r r' : Rec) (hrK : r ∈ K)
    (hr : ∀ y, allows r y ↔ reads d y = b) (hr' : ∀ y, allows r' y ↔ reads d y = !b) :
    allowed allows (insert r' K) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have h1 := (hr y).mp (hy r (Finset.mem_insert_of_mem hrK))
  have h2 := (hr' y).mp (hy r' (Finset.mem_insert_self r' K))
  rw [h1] at h2
  cases b <;> exact absurd h2 (by decide)

end APFPaper1.RecordOccupant

#print axioms APFPaper1.RecordOccupant.side_is_the_allowed_states
#print axioms APFPaper1.RecordOccupant.exactly_one_side_record_true
#print axioms APFPaper1.RecordOccupant.gains_the_allowed_states_side
#print axioms APFPaper1.RecordOccupant.no_tie_at_a_potential_state
#print axioms APFPaper1.RecordOccupant.other_side_never_after


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} {Rec : Type apfNative_u_3} (reads : D → X → Bool)
  (allows : Rec → X → Prop) (K : Finset.{apfNative_u_3} Rec) (x : X)
  (hx :
    @Membership.mem.{apfNative_u_1, apfNative_u_1} X (Set.{apfNative_u_1} X) (@Set.instMembership.{apfNative_u_1} X)
      (@APFPaper1.RecordOccupant.allowed.{apfNative_u_1, apfNative_u_3} X Rec allows K) x)
  (d : D) (b : Bool)
  (h : @APFPaper1.RecordOccupant.HasSide.{apfNative_u_1, apfNative_u_2, apfNative_u_3} X D Rec reads allows K d b),
  @Eq.{1} Bool (reads d x) b := by
  exact @APFPaper1.RecordOccupant.side_is_the_allowed_states
