-- Prove2me | solution 1 for APFPaper1.RecordOccupant.both_sides_can_be_gained
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:18:54.801531+00:00
-- url     : https://prove2.me/submissions/15ea413a-72e3-47c9-813d-1e05699f0cf8

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_gaining_a_side
title: Where the occupant is in raw form on a distinction, either side can be gained, gaining it puts the occupant in record form with that side, and if the two side records cost the same the two ways cost the same
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST: 18:46 "let's work on 3 next" (what picks the side when one is gained);
 18:57 "Yes" (where nothing is recorded the occupant itself has no side; RULING_occupant_forms_2026-11-14).
 Def_APFPaper1_RecordOccupant (this seat). Codebank apf/plec.py: check_Regime_exit_Type_II (under a
 symmetric cost "No symmetry-breaking selector is provided by the cost"), check_Regime_exit_Type_III (record
 locking), check_T_type_II_resolution_under_L_irr (records already kept tilt the cost; reading grade).
 apf/aeon_turnover.py, fence 1: "Occupancy is a contingent initial datum". Paper 5 companion, Continuation
 Symmetry and Degenerate Occupied Minima v1.7:219: "APF does not derive which continuation trajectories the
 world actually occupies." FOUNDATION_INPUTS B07b, whose header says no "result about A2 measuring or
 resolving ties is assumed".
consumes_inputs: none. Ordinary mathematics on the definitions.
named_hypotheses: hrt and hrf (the two records allow exactly the potential states on one side of d each);
 in the cost theorem, hc (the two side records cost the same), which is NOT adopted and is not said by any
 source read.
statement: (both_sides_can_be_gained) if the occupant is in raw form on d, the records with the record of
 side true added allow some potential state, and so do the records with the record of side false added.
 (gaining_a_side_gives_record_form) with either added, the occupant is in record form on d with that side.
 (gaining_either_side_costs_the_same) if neither side record is already kept and the two cost the same, the
 two enlarged sets of records cost the same.
not_claimed: that the two side records cost the same; that anything picks the side. Equal side-record
 prices give equal extended-record costs. Global minimum nonuniqueness additionally requires two distinct
 global minimizers; neither minimization nor a side selector is established here. No lane. No claim that the transfer is forced, that the
 carrier gap is closed or narrowed, or that Born is derived.
-/
import Definitions.Def_APFPaper1_RecordOccupant
import Mathlib.Data.Finset.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper1.RecordOccupant

variable {X D Rec : Type*}

/-- If the occupant is in raw form on `d`, either side can be gained: the enlarged records still
allow some potential state. -/
theorem both_sides_can_be_gained [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (hraw : NoSide reads allows K d)
    (rt rf : Rec) (hrt : ∀ y, allows rt y ↔ reads d y = true)
    (hrf : ∀ y, allows rf y ↔ reads d y = false) :
    (allowed allows (insert rt K)).Nonempty ∧ (allowed allows (insert rf K)).Nonempty := by
  obtain ⟨⟨x, hx, hxt⟩, ⟨y, hy, hyf⟩⟩ := hraw
  refine ⟨⟨x, fun s hs => ?_⟩, ⟨y, fun s hs => ?_⟩⟩
  · rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact (hrt x).mpr hxt
    · exact hx s hs'
  · rcases Finset.mem_insert.mp hs with rfl | hs'
    · exact (hrf y).mpr hyf
    · exact hy s hs'

/-- With the record of side `b` added, the occupant is in record form on `d` with side `b`,
provided some potential state is still allowed. -/
theorem gaining_a_side_gives_record_form [DecidableEq Rec] (reads : D → X → Bool)
    (allows : Rec → X → Prop) (K : Finset Rec) (d : D) (b : Bool) (r : Rec)
    (hr : ∀ y, allows r y ↔ reads d y = b) (hne : (allowed allows (insert r K)).Nonempty) :
    HasSide reads allows (insert r K) d b :=
  ⟨hne, fun y hy => (hr y).mp (hy r (Finset.mem_insert_self r K))⟩

/-- If neither side record is already kept and the two cost the same, the two enlarged sets of
records cost the same. -/
theorem gaining_either_side_costs_the_same [DecidableEq Rec] (K : Finset Rec) (rt rf : Rec)
    (hrt : rt ∉ K) (hrf : rf ∉ K) (cost : Rec → ℝ) (hc : cost rt = cost rf) :
    ∑ r ∈ insert rt K, cost r = ∑ r ∈ insert rf K, cost r := by
  rw [Finset.sum_insert hrt, Finset.sum_insert hrf, hc]

end APFPaper1.RecordOccupant

#print axioms APFPaper1.RecordOccupant.both_sides_can_be_gained
#print axioms APFPaper1.RecordOccupant.gaining_a_side_gives_record_form
#print axioms APFPaper1.RecordOccupant.gaining_either_side_costs_the_same


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} {Rec : Type apfNative_u_3}
  [inst : DecidableEq.{apfNative_u_3 + 1} Rec] (reads : D → X → Bool) (allows : Rec → X → Prop)
  (K : Finset.{apfNative_u_3} Rec) (d : D)
  (hraw : @APFPaper1.RecordOccupant.NoSide.{apfNative_u_1, apfNative_u_2, apfNative_u_3} X D Rec reads allows K d)
  (rt rf : Rec) (hrt : ∀ (y : X), Iff (allows rt y) (@Eq.{1} Bool (reads d y) Bool.true))
  (hrf : ∀ (y : X), Iff (allows rf y) (@Eq.{1} Bool (reads d y) Bool.false)),
  And
    (@Set.Nonempty.{apfNative_u_1} X
      (@APFPaper1.RecordOccupant.allowed.{apfNative_u_1, apfNative_u_3} X Rec allows
        (@Insert.insert.{apfNative_u_3, apfNative_u_3} Rec (Finset.{apfNative_u_3} Rec)
          (@Finset.instInsert.{apfNative_u_3} Rec inst) rt K)))
    (@Set.Nonempty.{apfNative_u_1} X
      (@APFPaper1.RecordOccupant.allowed.{apfNative_u_1, apfNative_u_3} X Rec allows
        (@Insert.insert.{apfNative_u_3, apfNative_u_3} Rec (Finset.{apfNative_u_3} Rec)
          (@Finset.instInsert.{apfNative_u_3} Rec inst) rf K))) := by
  exact @APFPaper1.RecordOccupant.both_sides_can_be_gained
