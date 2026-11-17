-- Prove2me | Definitions.Def_APFPaper5_K2_recorded_classes_Vocabulary
-- name    : APFPaper5_K2_recorded_classes_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:51:17.682192+00:00
-- url     : https://prove2.me/theorems/d9b0a2b6-dec4-4c3c-afd0-8f48d9c08add
-- title:
--   Model vocabulary — Costs and bounds for recorded classes
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   A recorded class is the Boolean list of records kept by the listed distinctions that read true. Its cost identity is definitional and its three-class bound requires nonnegative weights. Excluding a supplied turnTable from such lists does not exclude physical quantum turns or address the unrecorded state.
--
--   **Supplied data and hypotheses**
--
--   - Every parameter and hypothesis in the exact source declaration remains exposed; no author input is adopted.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Theorems.Thm_APFPaper5_K2_recorded_classes; Pullbacks v39, SHA-256 7b838b50b1566bc7bd9006c2d2840d9424bf5e9bb2adceae18b87e8d3e911c2b. Theorems.Thm_APFPaper5_K2_recorded_classes; pullbacks v39; SHA-256 7b838b50b1566bc7bd9006c2d2840d9424bf5e9bb2adceae18b87e8d3e911c2b

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

/-- The held family of a state: among the listed distinctions, those that read true on it. -/
def heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) : Finset D :=
  S.filter (fun d => reads d x = true)

/-- What is recorded of a state: the list of records its held family keeps. -/
def recordedClass (keeps : Finset D → W → Bool) (reads : D → X → Bool) (S : Finset D) (x : X) :
    W → ℝ :=
  keptClass keeps (heldFamily reads S x)











end APFPaper5.K2


