-- Prove2me | solution 1 for APFPaper5.K4.fixedByProducts_of_all_part_states
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:49:13.738488+00:00
-- url     : https://prove2.me/submissions/efb1ee30-b863-4842-bc44-31991fd2ba44

import Definitions.Def_APFPaper5_K4_fixed_by_products_needs_rates_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K4_fixed_by_products_needs_rates
title: If every reading of the joint record book is fixed by its values on products of admitted states of the two parts, and the recombination of AA' with BB' is an admitted joint state, then some admitted state of a part has a rate; with every state of a part admitted the condition holds
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:48: "Jointness stops at pairs". 21:06: "Yes" (to: the by-levels
 reading, with units being distinctions and recorded relations between two units; and to typing the link to
 K4). NOTE_carrier_gap_and_local_tomography_2026-11-14. Builder seat, K4: Def_APFPaper5_K4_JointCarrier,
 Def_APFPaper5_K4_CompositeOnly, Thm_APFPaper5_K4_composite_only_reading
 (reading_zero_on_products_is_zero, compositeOnly_zero_on_rateFree_products,
 compositeOnly_on_recombination). Paper 5 Supplement, field selection by split closed-world composite
 gates; codebank apf/closed_world_completeness.py check_T_split_composite_gates_tomographic_locality.
standing: CONDITIONAL THEOREMS in the builder seat's K4 model (two parts, each a pair of held components
 with a value and a rate). FixedByProducts is the author's by-levels reading AS IT WOULD BE SAID OF THE
 JOINT RECORD BOOK: a joint reading is fixed by its values on pairs made of one state of each part. That
 it is the right translation of "every joint record is a relation between two units" is a READING by this
 seat. It is not derived from any statement about records, and it is not ruled.
what this file says:
 1. some_part_state_has_a_rate. Under FixedByProducts, with the recombination of AA' and BB' admitted, the
    admitted states of a part are not all rate-free.
 2. fixedByProducts_of_all_part_states. If every state of a part is admitted, FixedByProducts holds for any
    set of joint states. So the condition can be met.
 3. not_fixedByProducts_of_rateFree. If only rate-free states of the parts are admitted and the
    recombination is admitted, FixedByProducts fails.
what this file does NOT say: that rates exist in any physical context; that the by-levels reading is true;
 that the recombination is admitted; anything about the continuum on one pair, the hold of K3, or tensor
 closure. It restates, from a named condition, what the builder seat's K4 and the codebank already carry.
 No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
 derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K4_reading_zero_on_products_is_zero
import Theorems.Thm_APFPaper5_K4_compositeOnly_is_product_of_rates
import Theorems.Thm_APFPaper5_K4_sums_of_books_differ_in_compositeOnly
import Theorems.Thm_APFPaper5_K4_compositeOnly_needs_own_record
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K4

open APFPaper5.K3



/-- If joint readings are fixed by products and the recombination of AA' with BB' is admitted, some
admitted state of a part has a rate. -/
theorem some_part_state_has_a_rate (admPart : Set Held2) (admJoint : Set Joint)
    (hrec : jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩) ∈ admJoint)
    (hlevels : FixedByProducts admPart admJoint) : ∃ h ∈ admPart, ¬ RateFree h := by
  by_contra hcon
  have hfree : ∀ h ∈ admPart, RateFree h := by
    intro h hh
    by_contra hnot
    exact hcon ⟨h, hh, hnot⟩
  have hz := hlevels compositeOnly
    (fun h hh k _ => compositeOnly_zero_on_rateFree_products h k (hfree h hh)) _ hrec
  rw [compositeOnly_on_recombination] at hz
  norm_num at hz

/-- With every state of a part admitted, joint readings are fixed by products. -/
theorem fixedByProducts_of_all_part_states (admJoint : Set Joint) :
    FixedByProducts Set.univ admJoint :=
  fun w h0 p _ =>
    reading_zero_on_products_is_zero w (fun h k => h0 h (Set.mem_univ h) k (Set.mem_univ k)) p

/-- With only rate-free states of the parts admitted, and the recombination admitted, joint readings are
not fixed by products. -/
theorem not_fixedByProducts_of_rateFree (admPart : Set Held2) (admJoint : Set Joint)
    (hfree : ∀ h ∈ admPart, RateFree h)
    (hrec : jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩) ∈ admJoint) :
    ¬ FixedByProducts admPart admJoint := by
  intro hlevels
  obtain ⟨h, hh, hnot⟩ := some_part_state_has_a_rate admPart admJoint hrec hlevels
  exact hnot (hfree h hh)

end APFPaper5.K4


theorem solution :
∀ (admJoint : Set.{0} APFPaper5.K4.Joint), APFPaper5.K4.FixedByProducts (@Set.univ.{0} APFPaper5.K3.Held2) admJoint := by
  exact @APFPaper5.K4.fixedByProducts_of_all_part_states
