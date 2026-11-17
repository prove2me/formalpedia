-- Prove2me | solution 1 for APFPaper1.RecordOccupant.any_two_part_states_are_one_state
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:31:56.480352+00:00
-- url     : https://prove2.me/submissions/e5aa57f9-f3bb-4695-ba94-c060d6a9f2e7

import Definitions.Def_APFPaper1_RecordOccupant_products_across_a_cut_Vocabulary
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



/-- Every potential state is a product across any cut: it has itself as both parts. -/
theorem every_state_is_a_product (reads : D → X → Bool) (A : Set D) [DecidablePred (· ∈ A)] (z : X) :
    IsProductAcross reads A z z z := by
  intro d
  split_ifs <;> rfl

/-- Under B02's second sentence, any state of the first part and any state of the second are the two
halves of one potential state, on any finite family of distinctions. -/
theorem any_two_part_states_are_one_state (reads : D → X → Bool)
    (hB02 : APFB02.EveryCombinationHeld reads) (A : Set D) [DecidablePred (· ∈ A)] (S : Finset D)
    (x y : X) : ∃ z : X, ∀ d ∈ S, reads d z = if d ∈ A then reads d x else reads d y :=
  hB02 S (fun d => if d ∈ A then reads d x else reads d y)

/-- A reading of potential states that vanishes on every product across the cut vanishes everywhere. -/
theorem fixed_by_products_is_automatic {β : Type*} [Zero β] (reads : D → X → Bool) (A : Set D)
    [DecidablePred (· ∈ A)] (R : X → β)
    (h0 : ∀ z x y : X, IsProductAcross reads A z x y → R z = 0) (z : X) : R z = 0 :=
  h0 z z z (every_state_is_a_product reads A z)

end APFPaper1.RecordOccupant


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} (reads : D → X → Bool)
  (hB02 : @APFB02.EveryCombinationHeld.{apfNative_u_1, apfNative_u_2} X D reads) (A : Set.{apfNative_u_2} D)
  [inst :
    @DecidablePred.{apfNative_u_2 + 1} D fun (x : D) =>
      @Membership.mem.{apfNative_u_2, apfNative_u_2} D (Set.{apfNative_u_2} D) (@Set.instMembership.{apfNative_u_2} D) A
        x]
  (S : Finset.{apfNative_u_2} D) (x y : X),
  @Exists.{apfNative_u_1 + 1} X fun (z : X) =>
    ∀ (d : D),
      @Membership.mem.{apfNative_u_2, apfNative_u_2} D (Finset.{apfNative_u_2} D)
          (@SetLike.instMembership.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} D) D
            (@Finset.instSetLike.{apfNative_u_2} D))
          S d →
        @Eq.{1} Bool (reads d z)
          (@ite.{1} Bool
            (@Membership.mem.{apfNative_u_2, apfNative_u_2} D (Set.{apfNative_u_2} D)
              (@Set.instMembership.{apfNative_u_2} D) A d)
            (inst d) (reads d x) (reads d y)) := by
  exact @APFPaper1.RecordOccupant.any_two_part_states_are_one_state
