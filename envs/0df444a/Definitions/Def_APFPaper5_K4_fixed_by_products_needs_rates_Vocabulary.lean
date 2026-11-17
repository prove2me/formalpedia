-- Prove2me | Definitions.Def_APFPaper5_K4_fixed_by_products_needs_rates_Vocabulary
-- name    : APFPaper5_K4_fixed_by_products_needs_rates_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:23:51.943468+00:00
-- url     : https://prove2.me/theorems/72d1837d-fa5f-4951-9436-3094385ce8b6
-- title:
--   Model vocabulary — A conditional product-reading criterion forces a rate
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   FixedByProducts is an uninstalled candidate interpretation, not derived from the by-levels record statement. Together with admission of the specified recombination it implies an admitted non-rate-free part state. No physical rates, tensor closure or K3/K4 completion are established.
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
--   Theorems.Thm_APFPaper5_K4_fixed_by_products_needs_rates; Pullbacks v39, SHA-256 583146169cf7a84c385e7cb035352532da4bccfc85494116585412468df9cb7e. Theorems.Thm_APFPaper5_K4_fixed_by_products_needs_rates; pullbacks v39; SHA-256 583146169cf7a84c385e7cb035352532da4bccfc85494116585412468df9cb7e

import Definitions.Def_APFPaper5_K4_CompositeOnly
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_APFPaper5_K4_reading_zero_on_products_is_zero
import Theorems.Thm_APFPaper5_K4_compositeOnly_is_product_of_rates
import Theorems.Thm_APFPaper5_K4_sums_of_books_differ_in_compositeOnly
import Theorems.Thm_APFPaper5_K4_compositeOnly_needs_own_record
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_composite_only_reading
title: With rates a joint reading is fixed by its values on products; without rates one joint reading is not, and it is the product of the two rates
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_CompositeOnly. The test agreed with the author on 2026-11-13.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition.
statement: (reading_zero_on_products_is_zero) a reading of the joint record book that is zero on every
 product is zero on every joint state.
 (compositeOnly_is_product_of_rates) on a product, the reading compositeOnly is minus twice the product of
 the two parts' rates.
 (compositeOnly_zero_on_rateFree_products, compositeOnly_on_recombination) so it is zero on every product of
 states with no rate, and it is one on a recombination of two such products.
 (rateFree_joint_state_fixed_by_parts_readings) for two joint states with no rate, written x and y: if the
 cost of AA', the cross terms of AA' with AB' and with BA', and the sum of the two cross terms across parts
 agree, the difference of the two cross terms across parts agrees as well.
 (sums_of_books_agree_on_parts_readings, sums_of_books_differ_in_compositeOnly) two pairs of joint states
 with no rate have the same total reading under every weighting that treats the two cross terms across
 parts alike, and different total readings under compositeOnly.
 (compositeOnly_needs_own_record) in a record model over pairs of joint states whose held records are fixed
 by such weightings of the total book, some reading of compositeOnly needs a record the family does not
 hold. Conditional on hsound, as in Thm_APFPaper5_K1_record_model_bridge.
reading: with rates, the joint record book is the parts' record books multiplied. Without rates it holds
 one reading more. A single joint state does not show the difference; a sum of two books does.
not_claimed: that record books of alternatives add; that a joint relation may hold no record of its own;
 hence no derivation of the rate. Any K.
-/










set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3





theorem compositeOnly_zero_on_rateFree_products (h k : Held2) (hh : RateFree h) :
    linearRecord compositeOnly (pair h k) = 0 := by
  rw [compositeOnly_is_product_of_rates]
  dsimp only [crossIm]
  rw [hh.1, hh.2]
  ring

theorem compositeOnly_on_recombination :
    linearRecord compositeOnly
      (jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩)) = 1 := by
  dsimp only [linearRecord, compositeOnly, jointAdd, pair]
  norm_num









end APFPaper5.K4

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






set_option autoImplicit false

namespace APFPaper5.K4

open APFPaper5.K3

/-- A reading that is linear in the joint record book and vanishes on every product of admitted states of
the two parts vanishes on every admitted joint state. -/
def FixedByProducts (admPart : Set Held2) (admJoint : Set Joint) : Prop :=
  ∀ w : RecordWeights, (∀ h ∈ admPart, ∀ k ∈ admPart, linearRecord w (pair h k) = 0) →
    ∀ p ∈ admJoint, linearRecord w p = 0







end APFPaper5.K4


