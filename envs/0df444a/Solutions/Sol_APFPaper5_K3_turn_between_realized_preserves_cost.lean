-- Prove2me | solution 1 for APFPaper5.K3.turn_between_realized_preserves_cost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:31:34.745604+00:00
-- url     : https://prove2.me/submissions/fa0d35a7-1a20-472a-8363-463859b46161

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_preservation_cost
title: Under the two preservation clauses, an admissible turn leaves cost unchanged
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K3_Continuity (TurnsLoseNothing) and Def_APFPaper5_K3_Preservation
 (TurnsNeverRaiseCost), both adopted on 2026-11-12. Thm_APFPaper5_K3_cost_invariant.
consumes_inputs: (turn_between_realized_preserves_cost) A2, in the written-out form of its formal reference
 A2Selection; fidelity of that form is NOT certified. The first theorem consumes none and is conditional on the
 two named hypotheses.
statement: (cost_invariant_of_preservation) if turns lose nothing and never raise cost, every admissible turn
 leaves cost unchanged. (turn_between_realized_preserves_cost) if a move carries every realized configuration
 of an admissible set to a realized configuration of the same set, it leaves the price of a realized
 configuration unchanged. Here realized is read as in A2: admissible, and no admissible configuration cheaper.
not_claimed: that an admissible turn carries realized configurations to realized configurations; that the
 price in A2 is the cost on combinations used in the plane theorem.
-/
import Definitions.Def_APFPaper5_K3_Preservation
import Theorems.Thm_APFPaper5_K3_cost_invariant_of_loseNothing
import Theorems.Thm_APFPaper5_K3_realized_cost_eq

set_option autoImplicit false
namespace APFPaper5.K3

universe u
variable {S : Type u}

theorem cost_invariant_of_preservation (Adm : Set (S → S)) (cost : S → ℝ)
    (h : TurnsLoseNothing Adm) (hc : TurnsNeverRaiseCost Adm cost) :
    ∀ f ∈ Adm, ∀ s : S, cost (f s) = cost s :=
  cost_invariant_of_loseNothing Adm h cost hc

theorem turn_between_realized_preserves_cost (admissible : Set S) (price : S → ℝ) (f : S → S)
    (hf : ∀ s : S, (s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a) →
      (f s ∈ admissible ∧ ∀ a ∈ admissible, price (f s) ≤ price a))
    (s : S) (hs : s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a) :
    price (f s) = price s :=
  realized_cost_eq admissible price (f s) s (hf s hs) hs

end APFPaper5.K3


universe apfNative_u
theorem solution :
∀ {S : Type apfNative_u} (admissible : Set.{apfNative_u} S) (price : S → Real) (f : S → S)
  (hf :
    ∀ (s : S),
      And
          (@Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
            admissible s)
          (∀ (a : S),
            @Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
                admissible a →
              @LE.le.{0} Real Real.instLE (price s) (price a)) →
        And
          (@Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
            admissible (f s))
          (∀ (a : S),
            @Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
                admissible a →
              @LE.le.{0} Real Real.instLE (price (f s)) (price a)))
  (s : S)
  (hs :
    And
      (@Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
        admissible s)
      (∀ (a : S),
        @Membership.mem.{apfNative_u, apfNative_u} S (Set.{apfNative_u} S) (@Set.instMembership.{apfNative_u} S)
            admissible a →
          @LE.le.{0} Real Real.instLE (price s) (price a))),
  @Eq.{1} Real (price (f s)) (price s) := by
  exact @APFPaper5.K3.turn_between_realized_preserves_cost
