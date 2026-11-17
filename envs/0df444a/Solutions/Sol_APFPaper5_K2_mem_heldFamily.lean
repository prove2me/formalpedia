-- Prove2me | solution 1 for APFPaper5.K2.mem_heldFamily
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T16:02:46.5215+00:00
-- url     : https://prove2.me/submissions/35b5c11d-903f-43b4-be4c-0df52b903078

import Definitions.Def_APFPaper5_K2_recorded_classes_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_recorded_classes
title: What is recorded: the class of a state is the list of records its held family keeps; its cost is the ledger's; any three such classes obey the record ledger's bound, so a turned mark is not among them
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 13:52 HST, "Seems like this is ok as it's about records which are not ever in
 superposition?", and 13:54 HST, "Yes" (RULING_C_for_what_is_recorded_2026-11-15): C for what is recorded;
 records are never in superposition; the unrecorded part is left to K3.
source: Def_APFPaper5_K2_StateClass (keptClass, recordForm); Thm_APFPaper5_K2_state_class_candidates
 (keptClass_cost); Thm_APFPaper5_K1_record_tables_and_turns (atomTable_triangle, turnTable). Paper 1
 Supplement v9.28:1829-1843 (a structural alignment: a carrier and the finite family of distinctions each
 reading 1 on it).
consumes_inputs: none.
definitions:
 - heldFamily: among listed distinctions, those that read true on the state.
 - recordedClass: the list of records the held family keeps.
theorems:
 - (mem_heldFamily) a distinction is in the held family exactly when it is listed and reads true.
 - (recordedClass_cost) the weighted overlap of the recorded class with itself is the cost of the records the
   held family keeps.
 - (keptClass_triangle, recorded_states_triangle) for costs that are never negative, the classes of any three
   held families, and so of any three states, obey the record ledger's bound.
 - (no_three_recorded_classes_have_turnTable) so no three recorded classes have the table of a mark, its
   turn and its double turn, for any turn strictly between none and the quarter turn.
reading: "records are never in superposition" is, as typed, that a recorded class is a list of records. A
 turned mark is then not a recorded class. Nothing here says what it is.
not claimed: anything about what a state holds that is not recorded; any action of a hold or a test on
 recorded classes. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed,
 or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_StateClass
import Theorems.Thm_APFPaper5_K2_atomTable_eq_recordForm
import Theorems.Thm_APFPaper5_K2_tableForm_atomTable_eq_recordForm
import Theorems.Thm_APFPaper5_K2_activeClass_after_hold_of_no_turn
import Theorems.Thm_APFPaper5_K2_activeClass_after_turn
import Theorems.Thm_APFPaper5_K2_activeClass_cost
import Theorems.Thm_APFPaper5_K2_shared_record_counts_four
import Theorems.Thm_APFPaper5_K2_sideClass_after_hold
import Theorems.Thm_APFPaper5_K2_opposite_sides_cancel
import Theorems.Thm_APFPaper5_K2_keptClass_cost
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint
import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_triangle
import Theorems.Thm_APFPaper5_K1_atomTable_le_diag
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_triangle
import Theorems.Thm_APFPaper5_K1_turnTable_symm
import Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
import Theorems.Thm_APFPaper5_K1_no_record_ledger_has_turnTable
import Theorems.Thm_APFPaper5_K1_no_three_distinctions_have_turnTable
import Theorems.Thm_APFPaper5_K1_turnTable_half_form
import Theorems.Thm_APFPaper5_K1_turnTable_half_nonneg
import Theorems.Thm_APFPaper5_K1_turnTable_half_faithful
import Theorems.Thm_APFPaper5_K1_ownTable_eq
import Theorems.Thm_APFPaper5_K1_turnClass_negative
import Theorems.Thm_APFPaper5_K1_turnTable_on_classes

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uX uD uW
variable {X : Type uX} {D : Type uD} {W : Type uW}





theorem mem_heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) (d : D) :
    d ∈ heldFamily reads S x ↔ d ∈ S ∧ reads d x = true :=
  Finset.mem_filter

/-- The cost of what is recorded of a state is the cost of the records its held family keeps. -/
theorem recordedClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool)
    (reads : D → X → Bool) (S : Finset D) (x : X) :
    recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S x) =
      keptCost w keeps (heldFamily reads S x) :=
  keptClass_cost w keeps (heldFamily reads S x)

/-- The classes of any three held families obey the record ledger's bound. -/
theorem keptClass_triangle [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (S T U : Finset D) :
    recordForm w (keptClass keeps S) (keptClass keeps T) +
        recordForm w (keptClass keeps S) (keptClass keeps U) -
        recordForm w (keptClass keeps T) (keptClass keeps U) ≤
      recordForm w (keptClass keeps S) (keptClass keeps S) :=
  atomTable_triangle w hw (fun (F : Finset D) (a : W) => keeps F a) S T U

/-- So do the recorded classes of any three states. -/
theorem recorded_states_triangle [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (reads : D → X → Bool) (S : Finset D) (x y z : X) :
    recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S y) +
        recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S z) -
        recordForm w (recordedClass keeps reads S y) (recordedClass keeps reads S z) ≤
      recordForm w (recordedClass keeps reads S x) (recordedClass keeps reads S x) :=
  keptClass_triangle w hw keeps _ _ _

/-- No three recorded classes have the table of a mark, its turn and its double turn. -/
theorem no_three_recorded_classes_have_turnTable [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (keeps : Finset D → W → Bool) (F : Fin 3 → Finset D) (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    ¬ ∀ i j, recordForm w (keptClass keeps (F i)) (keptClass keeps (F j)) = turnTable t i j :=
  no_record_ledger_has_turnTable w hw (fun (i : Fin 3) (a : W) => keeps (F i) a) t h0 h1

end APFPaper5.K2


universe apfNative_uX apfNative_uD
theorem solution :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (S : Finset.{apfNative_uD} D) (x : X) (d : D),
  Iff
    (@Membership.mem.{apfNative_uD, apfNative_uD} D (Finset.{apfNative_uD} D)
      (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} D) D
        (@Finset.instSetLike.{apfNative_uD} D))
      (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} X D reads S x) d)
    (And
      (@Membership.mem.{apfNative_uD, apfNative_uD} D (Finset.{apfNative_uD} D)
        (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} D) D
          (@Finset.instSetLike.{apfNative_uD} D))
        S d)
      (@Eq.{1} Bool (reads d x) Bool.true)) := by
  exact @APFPaper5.K2.mem_heldFamily
