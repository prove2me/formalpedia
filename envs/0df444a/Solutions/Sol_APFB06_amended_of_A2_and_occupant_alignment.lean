-- Prove2me | solution 1 for APFB06.amended_of_A2_and_occupant_alignment
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:11.285359+00:00
-- url     : https://prove2.me/submissions/dff7d210-318f-494d-88ef-5ff76d72c253

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB06_occupant_alignment_holds
title: An occupant holds every distinction of its family by the definition of an alignment, and still holds them when nothing acts; so A2 at the protocol binding gives B06's declared form with no separate "holds its family there" hypothesis
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-13 16:19 HST ("Holds the family there can be derived, that's the
 alignment of the occupant that holds until acted upon"). FOUNDATION_INPUTS B06 in declared form, whose
 definition node says of OriginalAlignment.active: "The active clause is the definition of an alignment
 (P1:1831-1836), not ... an additional physical law". B01's quotient. Def_APFB07a_ProtocolBinding.
 Thm_APFB06_occupancy_from_A2, whose hypothesis hdet this node removes.
consumes_inputs: A2 in declared form at the protocol binding, in the last theorem; B06's declared form is its
 CONCLUSION. The first two theorems use only the definition of an alignment and B01's quotient. The formal
 fidelity of A2 is NOT CERTIFIED.
statement: (APFB06.occupant_holds_its_family) an alignment that carries a family holds every distinction of
 the family at its carrier. This is the active clause read off.
 (APFB06.alignment_holds_under_no_action) processes are words. If the state after the empty word admits
 exactly what the state admitted, then the state after the empty word is the same physical object, so every
 distinction an alignment at that object carries is still held.
 (APFB06.amended_of_A2_and_occupant_alignment) occupant gives, for each task family, an alignment that
 carries it. If the realized protocol of each family is admitted at a raw state of that alignment's carrier
 (hstart), then for every nonempty task family the amended B06 holds at the extensional joint class, with
 the actual alignment the occupant's.
reading: "holds its family there" is not a law about protocols. It is what an alignment is. What is still
 assumed is that the realization is an alignment of the interface's family, and that the realized protocol
 starts at it.
not_claimed: anything about where a run of the protocol ends or what the family reads there; that is the hold
 sentence. That the realization is an alignment; hstart; any identification of B06's tasks with the raw
 distinctions of B02, B03 and B05.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.occupant_holds_its_family {X Q : Type*} (Cont : X → Q → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (o : APFB06.OriginalAlignment Cont Dset)
    (S : Finset (APFB06.Task Cont Dset)) (h : o.carried = S) :
    ∀ d ∈ S, d.val o.carrier = true := by
  rw [← h]
  exact o.active

theorem APFB06.alignment_holds_under_no_action {X A : Type*} (Cont : X → List A → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (after : X → List A → X) (x : X)
    (hder : ∀ w : List A, Cont (after x []) w ↔ Cont x ([] ++ w))
    (o : APFB06.OriginalAlignment Cont Dset) (ho : o.carrier = APFB01.physicalClass Cont x) :
    ∀ d ∈ o.carried, d.val (APFB01.physicalClass Cont (after x [])) = true := by
  have hsame : APFB01.physicalClass Cont (after x []) = APFB01.physicalClass Cont x := by
    apply Quot.sound
    funext w
    apply propext
    rw [hder w, List.nil_append]
  rw [hsame, ← ho]
  exact o.active

theorem APFB06.amended_of_A2_and_occupant_alignment
    {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : NNReal) (realized : Finset (APFB06.Task Cont Dset) → {p // p ∈ protocols})
    (hA2 : APFB07a.A2Selection (Interface := Finset (APFB06.Task Cont Dset))
      (Configuration := fun _ => {p // p ∈ protocols})
      (fun S p => APFB07a.protocolAdmissible wholeResource calibration maintained sufficient
        usesToRealize (C : ℝ) S p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (occupant : Finset (APFB06.Task Cont Dset) → APFB06.OriginalAlignment Cont Dset)
    (hfam : ∀ S : Finset (APFB06.Task Cont Dset), (occupant S).carried = S)
    (hstart : ∀ S : Finset (APFB06.Task Cont Dset),
      ∃ x : Raw, APFB01.physicalClass Cont x = (occupant S).carrier ∧ Cont x (realized S).val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, ∃ T : Finset (APFB06.Task Cont Dset), o.2 = occupant T) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by
  obtain ⟨⟨hserve, hC⟩, _⟩ := hA2 S
  have hC' : ((calibration (wholeResource (realized S)) : NNReal) : ℝ) ≤ ((C : NNReal) : ℝ) := hC
  obtain ⟨x, _, hx⟩ := hstart S
  have hserve' : APFB07a.Serves maintained sufficient usesToRealize (occupant S).carried
      (realized S) := by
    rw [hfam S]
    exact hserve
  refine ⟨{⟨(), occupant S⟩}, ?_, ⟨(), occupant S⟩, Set.mem_singleton _, ?_, ?_, realized S,
    hserve', x, hx⟩
  · intro o' ho'
    exact ⟨S, by rw [Set.mem_singleton_iff.mp ho']⟩
  · show (occupant S).carried.Nonempty
    rw [hfam S]
    exact hS
  · refine le_trans (sInf_le ⟨realized S, hserve', rfl⟩) ?_
    exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hC')


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {Raw : Type apfNative_u_1} {FullProcess : Type apfNative_u_2} {Resource : Type apfNative_u_3}
  {Record : Type apfNative_u_4} (Cont : Raw → FullProcess → Prop)
  (Dset : Set.{apfNative_u_1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
  (protocols : Set.{apfNative_u_2} FullProcess)
  (wholeResource :
    (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) →
      Resource)
  (calibration : Resource → NNReal)
  (maintained :
    (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) →
      Set.{apfNative_u_4} Record)
  (sufficient :
    (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) →
      Set.{apfNative_u_4} Record → @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset → Prop)
  (usesToRealize :
    (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) →
      @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset → Set.{apfNative_u_4} Record → Prop)
  (C : NNReal)
  (realized :
    Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) →
      @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, apfNative_u_2}
      (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
      (fun (x : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) =>
        @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
          @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
            (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
      (fun (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
          (p :
            @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) =>
        @APFB07a.protocolAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4}
          (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
          (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
            @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
              (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
          Resource Record wholeResource calibration maintained sufficient usesToRealize (NNReal.toReal C) S p)
      (fun (x : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
          (p :
            @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) =>
        @APFB07a.protocolBill.{apfNative_u_2, apfNative_u_3}
          (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
            @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
              (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
          Resource wholeResource calibration p)
      realized)
  (occupant :
    Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) →
      @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
  (hfam :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)),
      @Eq.{apfNative_u_1 + 1}
        (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
        (@APFB06.OriginalAlignment.carried.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset (occupant S)) S)
  (hstart :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)),
      @Exists.{apfNative_u_1 + 1} Raw fun (x : Raw) =>
        And
          (@Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
            (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x)
            (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset (occupant S)))
          (Cont x
            (@Subtype.val.{apfNative_u_2 + 1} FullProcess
              (fun (p : FullProcess) =>
                @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                  (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
              (realized S))))
  (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
  (hS : @Finset.Nonempty.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) S),
  @Exists.{apfNative_u_1 + 1}
    (Set.{apfNative_u_1}
      (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
        @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
    fun
      (actualJoint :
        Set.{apfNative_u_1}
          (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
            @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) =>
    And
      (∀
        (o :
          @Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
            @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
        @Membership.mem.{apfNative_u_1, apfNative_u_1}
            (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
              @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
            (Set.{apfNative_u_1}
              (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
                @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
            (@Set.instMembership.{apfNative_u_1}
              (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
                @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
            actualJoint o →
          @Exists.{apfNative_u_1 + 1}
            (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
            fun (T : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) =>
            @Eq.{apfNative_u_1 + 1} (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (@Sigma.snd.{0, apfNative_u_1} Unit
                (fun (x : Unit) => @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                o)
              (occupant T))
      (@APFB06.AmendedB06_20260914.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3} Unit (fun (x : Unit) => Raw)
        (fun (x : Unit) => FullProcess) (fun (x : Unit) => Resource) (fun (x : Unit) => Cont) (fun (x : Unit) => Dset)
        (fun (x : Unit) => protocols)
        (fun (x : Unit)
            (T : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) =>
          @Set.ofPred.{apfNative_u_2}
            (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
            fun
              (p :
                @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
                  @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                    (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) =>
            @APFB07a.Serves.{apfNative_u_1, apfNative_u_2, apfNative_u_4}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
                @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                  (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
              Record maintained sufficient usesToRealize T p)
        (fun (x : Unit) => wholeResource) (fun (x : Unit) => calibration) (fun (x : Unit) => C) actualJoint) := by
  exact @APFB06.amended_of_A2_and_occupant_alignment
