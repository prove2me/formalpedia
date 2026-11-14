-- Prove2me | solution 1 for APFB05.realized_has_no_removable_novel
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:03.762197+00:00
-- url     : https://prove2.me/submissions/776065b0-7195-47b6-a5ce-83f7da65b6c2

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB05_A2_economy
title: Economy: the family at the cost minimum carries no support-novel distinction that an admissible family does without
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B05 ("Genuinely new, support-novel distinctions have a uniform positive marginal
 cost floor") in its declared Lean form APFB05.MarginalFloor. FOUNDATION_INPUTS B07a, A2 ("Realization is the
 minimum-cost admissible configuration").
consumes_inputs: B05, in its declared form. A2 ONLY IN WRITTEN-OUT FORM on a supplied set of families: the
 hypothesis hA2 says the actual family is in the set and no family in the set costs less. The scope note of
 B07a says that a selector on supplied data does not certify the full physical statement, and the formal
 fidelity of A2 is NOT CERTIFIED. This theorem therefore does not certify a consumption of A2.
statement: (APFB05.novel_extra_costs_more) adding a tested support-novel distinction to an admissible family,
 with the larger family admissible, strictly raises the family cost.
 (APFB05.realized_has_no_removable_novel) if the actual family is at the cost minimum of a set of families,
 and S is in that set, the actual family is not S with a tested support-novel distinction added.
not_claimed: that any structure of the K layer is a support-novel distinction; that the smaller family is
 admissible in any given case; the physical statement of A2.
-/
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source

section
variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.novel_extra_costs_more
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (d : D g) (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d) :
    familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S <
      familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
        (insert d S) := by
  have h := (hB05 g).2 S d htested hS hSd hnew
  have heps := (hB05 g).1
  linarith

theorem APFB05.realized_has_no_removable_novel
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (families : Set (Finset (D g))) (actual : Finset (D g))
    (hA2 : actual ∈ families ∧ ∀ a ∈ families,
      familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
          actual ≤
        familyCost (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) a)
    (S : Finset (D g)) (d : D g) (hSmem : S ∈ families) (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d) :
    actual ≠ insert d S := by
  intro hact
  have hlt := APFB05.novel_extra_costs_more wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g S d htested hS hSd hnew
  have hle := hA2.2 S hSmem
  rw [hact] at hle
  linarith

end


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5
theorem solution :
∀ {Context : Type apfNative_u_1} {D : Context → Type apfNative_u_2} {P : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  [inst : (g : Context) → DecidableEq.{apfNative_u_2 + 1} (D g)] (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal) (maintained : (g : Context) → P g → Set.{apfNative_u_5} (Record g))
  (sufficient : (g : Context) → P g → Set.{apfNative_u_5} (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set.{apfNative_u_5} (Record g) → Prop)
  (tested : (g : Context) → D g → Prop) (C epsilon : Context → Real)
  (hB05 :
    @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R
      Record inst wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
  (g : Context) (families : Set.{apfNative_u_2} (Finset.{apfNative_u_2} (D g))) (actual : Finset.{apfNative_u_2} (D g))
  (hA2 :
    And
      (@Membership.mem.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} (D g))
        (Set.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)))
        (@Set.instMembership.{apfNative_u_2} (Finset.{apfNative_u_2} (D g))) families actual)
      (∀ (a : Finset.{apfNative_u_2} (D g)),
        @Membership.mem.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} (D g))
            (Set.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)))
            (@Set.instMembership.{apfNative_u_2} (Finset.{apfNative_u_2} (D g))) families a →
          @LE.le.{0} Real Real.instLE
            (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
              (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) actual)
            (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
              (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) a)))
  (S : Finset.{apfNative_u_2} (D g)) (d : D g)
  (hSmem :
    @Membership.mem.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} (D g))
      (Set.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)))
      (@Set.instMembership.{apfNative_u_2} (Finset.{apfNative_u_2} (D g))) families S)
  (htested : tested g d)
  (hS :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g) S)
  (hSd :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d S))
  (hnew :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S d),
  @Ne.{apfNative_u_2 + 1} (Finset.{apfNative_u_2} (D g)) actual
    (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
      (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d S) := by
  exact @APFB05.realized_has_no_removable_novel
