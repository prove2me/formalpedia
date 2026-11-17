-- Prove2me | Definitions.Def_APFPaper1_RecordOccupant_products_across_a_cut_Vocabulary
-- name    : APFPaper1_RecordOccupant_products_across_a_cut_Vocabulary
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:20:15.659741+00:00
-- url     : https://prove2.me/theorems/bd4acb68-f122-471b-a455-acf8140e57b0
-- title:
--   Model vocabulary — Products of Boolean readings across a cut
-- statement:
--   Data, predicates and immediate constructor helpers for this reviewed model. Its substantive results are published as separate proved theorem nodes.
--
--   IsProductAcross is equality of readings on the two sides of a cut. Every state is its own such product; EveryCombinationHeld gives finite recombination. This is not quantum state factorization or physical local tomography.
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
--   Theorems.Thm_APFPaper1_RecordOccupant_products_across_a_cut; Pullbacks v39, SHA-256 5076686a0b996cdce81f0bc04d7e6a785ccd4e30e78d18dcb8dadf0c87c14beb. Theorems.Thm_APFPaper1_RecordOccupant_products_across_a_cut; pullbacks v39; SHA-256 5076686a0b996cdce81f0bc04d7e6a785ccd4e30e78d18dcb8dadf0c87c14beb

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper1_RecordOccupant_products_across_a_cut
title: Among potential states of two-sided marks every state is a product across any cut, and under B02's second sentence any state of one part and any state of the other are the two halves of one state; so "fixed by its values on products" holds of every reading there and says nothing
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:20 HST: "Attempt" (the carry-over from the by-levels statement for
 two-sided marks to the condition of pass 32 on the builder seat's joint record book, FixedByProducts).
 Def_APFB02_EachTakesBothSides (APFB02.EveryCombinationHeld; B02's second sentence, inputs revision
 2026-11-14.1). Thm_APFPaper1_RecordOccupant_units_and_levels and
 Thm_APFPaper5_K4_fixed_by_products_needs_rates (this seat).
standing: THEOREMS, recording why the attempted carry-over does NOT go through from the two-sided statement
 alone. Not a countermodel to the builder seat's K4 results and not a statement about them.
what this file says:
 1. every_state_is_a_product. Across any cut of the distinctions, every potential state has itself as both
    parts.
 2. any_two_part_states_are_one_state. Under B02's second sentence, for any finite family, any state of
    the first part and any state of the second are the two halves of one potential state.
 3. fixed_by_products_is_automatic. A reading of potential states that vanishes on every product vanishes
    everywhere. No hypothesis on the reading.
reading: the condition of pass 32 has content only for joint states that are not products, which in the
 builder seat's K4 model are the recombinations of products. The typing of potential states with two-sided
 marks has no such states: by B02's second sentence every combination of sides is held. So a statement
 about records of two-sided marks cannot by itself yield the pass-32 condition. What is missing is a
 joint state that is a recombination, with a record book of its own. That is raw form with values, which
 is the carrier question, and nothing here bears on it.
what this file does NOT say: that the pass-32 condition is false; that the by-levels statement is false;
 anything about rates, a continuum or tensor closure. No lane. No claim that the transfer is forced, that
 the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false

namespace APFPaper1.RecordOccupant

variable {X D : Type*}

/-- Across the cut `A`, the state `z` has `x` as its first part and `y` as its second. -/
def IsProductAcross (reads : D → X → Bool) (A : Set D) [DecidablePred (· ∈ A)] (z x y : X) : Prop :=
  ∀ d, reads d z = if d ∈ A then reads d x else reads d y







end APFPaper1.RecordOccupant


