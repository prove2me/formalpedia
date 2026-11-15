-- Prove2me | solution 1 for APFB07a.familyCost_attained_of_A2
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:00:28.195812+00:00
-- url     : https://prove2.me/submissions/3252fe6f-7e16-4f60-a8a4-10f7c728a518

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07a_protocol_binding
title: Under the protocol binding, A2 says the family cost of each task family is attained by the realized protocol, and BW says no other admissible protocol has the same bill
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFB07a_ProtocolBinding. FOUNDATION_INPUTS B07a, B07b in declared form. Def_APFPaper1_FamilyCost.
consumes_inputs: A2 (APFB07a.A2Selection) and BW (APFB07b.BWUniqueMinimum) in declared form, at the
 CANDIDATE protocol binding of domain and price. The actual realization is a supplied argument. The formal
 fidelity of A2 is NOT CERTIFIED; this node does not certify it.
statement: (APFB07a.familyCost_attained_of_A2) if A2 holds at the protocol binding, then for every task
 family the family is feasible, its family cost equals the bill of the realized protocol, and it is
 ledger-admissible at the capacity. The infimum in the ledger's family cost is a minimum, and the realized
 protocol attains it.
 (APFB07a.realized_bill_gap_of_cost_gap) so a gap between two family costs is the same gap between the
 bills of the two realized protocols.
 (APFB07b.realized_protocol_unique_at_its_bill) if BW also holds at the binding, an admissible protocol
 with the bill of the realized one is the realized one.
reading: this is the form in which A2 touches the shared cost vocabulary of B03, B05 and B06 without
 changing the task, the support data, the calibration or the whole-resource account.
not_claimed: that the source's domain and price are this binding; that the realized protocol is the
 occupant's protocol of B06; anything about histories or about families of different tasks.
-/
import Definitions.Def_APFB07a_ProtocolBinding
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open APFPaper1.Source

theorem APFB07a.familyCost_attained_of_A2 {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (realized : Finset D → P)
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized) (S : Finset D) :
    familyFeasible maintained sufficient usesToRealize S ∧
      familyCost wholeResource calibration maintained sufficient usesToRealize S =
        APFB07a.protocolBill wholeResource calibration (realized S) ∧
      familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S := by
  obtain ⟨⟨hserve, hC⟩, hmin⟩ := hA2 S
  have hfeas : familyFeasible maintained sufficient usesToRealize S := ⟨realized S, hserve⟩
  have hcost : familyCost wholeResource calibration maintained sufficient usesToRealize S =
      APFB07a.protocolBill wholeResource calibration (realized S) := by
    have hmem : APFB07a.protocolBill wholeResource calibration (realized S) ∈
        {c : ℝ | ∃ p : P, (∀ d ∈ S, ∃ sigma : Set Record,
          sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ∧
          (calibration (wholeResource p) : ℝ) = c} := ⟨realized S, hserve, rfl⟩
    apply le_antisymm
    · exact csInf_le ⟨0, by rintro c ⟨p, _, rfl⟩; exact NNReal.coe_nonneg _⟩ hmem
    · refine le_csInf ⟨_, hmem⟩ ?_
      rintro c ⟨p, hp, rfl⟩
      by_cases hpC : APFB07a.protocolBill wholeResource calibration p ≤ C
      · exact hmin p ⟨hp, hpC⟩
      · exact le_trans hC (le_of_lt (not_le.mp hpC))
  exact ⟨hfeas, hcost, hfeas, by rw [hcost]; exact hC⟩

theorem APFB07a.realized_bill_gap_of_cost_gap {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (realized : Finset D → P)
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (S S' : Finset D) (eps : ℝ)
    (hgap : eps ≤ familyCost wholeResource calibration maintained sufficient usesToRealize S' -
      familyCost wholeResource calibration maintained sufficient usesToRealize S) :
    APFB07a.protocolBill wholeResource calibration (realized S) + eps ≤
      APFB07a.protocolBill wholeResource calibration (realized S') := by
  rw [(APFB07a.familyCost_attained_of_A2 wholeResource calibration maintained sufficient
      usesToRealize C realized hA2 S).2.1,
    (APFB07a.familyCost_attained_of_A2 wholeResource calibration maintained sufficient
      usesToRealize C realized hA2 S').2.1] at hgap
  linarith

theorem APFB07b.realized_protocol_unique_at_its_bill {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (C : ℝ) (realized : Finset D → P)
    (hA2 : APFB07a.A2Selection (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (hBW : APFB07b.BWUniqueMinimum (Interface := Finset D) (Configuration := fun _ => P)
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p))
    (S : Finset D) (p : P)
    (hp : APFB07a.protocolAdmissible wholeResource calibration maintained sufficient usesToRealize
      C S p)
    (hbill : APFB07a.protocolBill wholeResource calibration p =
      APFB07a.protocolBill wholeResource calibration (realized S)) : p = realized S := by
  obtain ⟨G0, _, huniq⟩ := hBW S
  have hr := hA2 S
  have hpmin : APFB07b.IsMinimum
      (fun q => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize C S q)
      (fun q => APFB07a.protocolBill wholeResource calibration q) p :=
    ⟨hp, fun K hK => by
      show APFB07a.protocolBill wholeResource calibration p ≤ _
      rw [hbill]
      exact hr.2 K hK⟩
  rw [huniq p hpmin, huniq (realized S) hr]


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (C : Real) (realized : Finset.{apfNative_u_1} D → P)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, apfNative_u_2} (Finset.{apfNative_u_1} D)
      (fun (x : Finset.{apfNative_u_1} D) => P)
      (fun (S : Finset.{apfNative_u_1} D) (p : P) =>
        @APFB07a.protocolAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
          wholeResource calibration maintained sufficient usesToRealize C S p)
      (fun (x : Finset.{apfNative_u_1} D) (p : P) =>
        @APFB07a.protocolBill.{apfNative_u_2, apfNative_u_3} P R wholeResource calibration p)
      realized)
  (S : Finset.{apfNative_u_1} D),
  And
    (@APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S)
    (And
      (@Eq.{1} Real
        (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
          wholeResource calibration maintained sufficient usesToRealize S)
        (@APFB07a.protocolBill.{apfNative_u_2, apfNative_u_3} P R wholeResource calibration (realized S)))
      (@APFPaper1.Source.familyAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize C S)) := by
  exact @APFB07a.familyCost_attained_of_A2
