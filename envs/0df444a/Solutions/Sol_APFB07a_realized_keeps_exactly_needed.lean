-- Prove2me | solution 1 for APFB07a.realized_keeps_exactly_needed
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T18:49:28.787515+00:00
-- url     : https://prove2.me/submissions/c1549495-f299-4160-bb8b-97f719f9a97c

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFB07a_realized_keeps_needed
title: At the protocol binding, the protocol A2 selects keeps every record its family needs, and keeps nothing else when some admitted protocol keeps exactly those records
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a in declared form. Def_APFB07a_ProtocolBinding and
 APFB07a.familyCost_attained_of_A2 (seat 01WrrBvu, unchanged). RULING_A2_protocol_binding_2026-11-13 (the
 author, 16:14 HST: A2's domain at an interface is the protocols that serve the interface's task family
 within capacity, and its price is the calibrated bill). Thm_APFPaper1_familyCost_count (the availability
 clause). Paper 0, sec:argmin_scope (read by the builder seat in v6.3.2; not reopened here).
consumes_inputs: A2 (APFB07a.A2Selection) in declared form at the protocol binding. The formal fidelity of
 A2 is NOT CERTIFIED; this node does not certify it. The actual realization is a supplied argument.
named_hypotheses: hbill, hkept, hneed and, in the second theorem, the availability clause havail, as in
 Thm_APFPaper1_familyCost_count.
statement: (realized_keeps_needed) under A2 at the protocol binding, with hkept and hneed, the selected
 protocol of a family keeps every record the family needs. (realized_keeps_exactly_needed) with hbill and
 the availability clause at the family as well, it keeps exactly those records.
reading: the form "no free rider" takes at the affirmed binding. Thm_APFB05_no_free_rider states it for
 A2 on a supplied set of candidate families; here the family is fixed and the candidates are protocols.
not_claimed: the availability clause; without it the selected protocol can keep a record its family does
 not need (Thm_APFB06_A2_keeps_unneeded_world). That the selected protocol is the occupant's protocol of
 B06. Weighted records.
-/
import Theorems.Thm_APFB07a_familyCost_attained_of_A2
import Theorems.Thm_APFB07b_realized_protocol_unique_at_its_bill
import Theorems.Thm_APFPaper1_Source_needed_subset_kept
import Theorems.Thm_APFPaper1_Source_card_needed_le_bill
import Theorems.Thm_APFPaper1_Source_card_needed_le_familyCost
import Theorems.Thm_APFPaper1_Source_familyCost_eq_card_of_available
import Theorems.Thm_APFPaper1_Source_join_of_available

set_option autoImplicit false
open APFPaper1.Source

section
variable {D P R Record : Type*} [DecidableEq Record]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)
  (kept : P → Finset Record) (fam : D → Finset Record)
  (C : ℝ) (realized : Finset D → P)

theorem APFB07a.realized_keeps_needed
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D) :
    S.biUnion fam ⊆ kept (realized S) :=
  needed_subset_kept maintained sufficient usesToRealize kept fam hkept hneed S (realized S)
    (hA2 S).1.1

theorem APFB07a.realized_keeps_exactly_needed
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hbill : ∀ p : P, (calibration (wholeResource p) : ℝ) = ((kept p).card : ℝ))
    (hkept : ∀ p : P, maintained p = (↑(kept p) : Set Record))
    (hneed : ∀ (p : P) (sigma : Set Record) (d : D),
      sufficient p sigma d → (↑(fam d) : Set Record) ⊆ sigma)
    (S : Finset D)
    (havail : ∃ p : P, kept p = S.biUnion fam ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) :
    kept (realized S) = S.biUnion fam := by
  have hsub := APFB07a.realized_keeps_needed wholeResource calibration maintained sufficient
    usesToRealize kept fam C realized hA2 hkept hneed S
  have hcost : familyCost wholeResource calibration maintained sufficient usesToRealize S =
      (calibration (wholeResource (realized S)) : ℝ) :=
    (APFB07a.familyCost_attained_of_A2 wholeResource calibration maintained sufficient
      usesToRealize C realized hA2 S).2.1
  have hcount := familyCost_eq_card_of_available wholeResource calibration maintained sufficient
    usesToRealize kept fam hbill hkept hneed S havail
  have hreal : ((kept (realized S)).card : ℝ) = ((S.biUnion fam).card : ℝ) := by
    rw [← hbill (realized S), ← hcost]
    exact hcount
  have hcard : (kept (realized S)).card ≤ (S.biUnion fam).card := by
    exact_mod_cast le_of_eq hreal
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

end


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_4 + 1} Record] (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (fam : D → Finset.{apfNative_u_4} Record) (C : Real) (realized : Finset.{apfNative_u_1} D → P)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, apfNative_u_2} (Finset.{apfNative_u_1} D)
      (fun (x : Finset.{apfNative_u_1} D) => P)
      (fun (S : Finset.{apfNative_u_1} D) (p : P) =>
        @APFB07a.protocolAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
          wholeResource calibration maintained sufficient usesToRealize C S p)
      (fun (x : Finset.{apfNative_u_1} D) (p : P) =>
        @APFB07a.protocolBill.{apfNative_u_2, apfNative_u_3} P R wholeResource calibration p)
      realized)
  (hbill :
    ∀ (p : P),
      @Eq.{1} Real (NNReal.toReal (calibration (wholeResource p)))
        (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{apfNative_u_4} Record (kept p))))
  (hkept :
    ∀ (p : P),
      @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) (maintained p)
        (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
          (@Finset.instSetLike.{apfNative_u_4} Record) (kept p)))
  (hneed :
    ∀ (p : P) (sigma : Set.{apfNative_u_4} Record) (d : D),
      sufficient p sigma d →
        @LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record)
          (@SetLike.coe.{apfNative_u_4, apfNative_u_4} (Finset.{apfNative_u_4} Record) Record
            (@Finset.instSetLike.{apfNative_u_4} Record) (fam d))
          sigma)
  (S : Finset.{apfNative_u_1} D)
  (havail :
    @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
      And
        (@Eq.{apfNative_u_4 + 1} (Finset.{apfNative_u_4} Record) (kept p)
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam))
        (∀ (d : D),
          @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
                (@Finset.instSetLike.{apfNative_u_1} D))
              S d →
            @Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
              And
                (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
                  (maintained p))
                (And (sufficient p sigma d) (usesToRealize p d sigma)))),
  @Eq.{apfNative_u_4 + 1} (Finset.{apfNative_u_4} Record) (kept (realized S))
    (@Finset.biUnion.{apfNative_u_1, apfNative_u_4} D Record inst S fam) := by
  exact @APFB07a.realized_keeps_exactly_needed
