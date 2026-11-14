-- Prove2me | solution 1 for APFB06.amended_of_A2_at_protocol_binding
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:58:09.404205+00:00
-- url     : https://prove2.me/submissions/f789d793-1cb3-4958-a5e8-16347abc89ca

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB06_occupancy_from_A2
title: If the actual alignment at an interface is the one its realized protocol determines, then A2 at the protocol binding gives B06's declared form for every nonempty task family
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's rulings of 2026-11-13: 16:14 HST ("Yes protocol is binding, at the interface it's the
 occupants alignment as determined by the protocol?"; RULING_A2_protocol_binding_2026-11-13.md) and 15:54 HST
 (B06's joint class is the extensional one; project doc RULING_joint_class_2026-11-13, sibling seat).
 FOUNDATION_INPUTS B06 and B07a in declared form. Def_APFB07a_ProtocolBinding.
consumes_inputs: A2 (APFB07a.A2Selection) in declared form at the protocol binding, with the tasks taken to
 be B06's tasks (two-valued functions on physical objects). B06's declared form is the CONCLUSION, at the
 extensional joint class. The formal fidelity of A2 is NOT CERTIFIED.
statement: (APFB06.amended_of_A2_at_protocol_binding) carrierOf gives, for each protocol, the physical object
 its alignment sits at. Suppose (hdet) a protocol that serves a family holds every member of the family at
 that object, and (hstart) each protocol is admitted at a raw state of that object. Then for every nonempty
 task family S there is a set of alignments, each sitting at the object determined by the realized protocol
 of its own family, for which the amended B06 holds: the alignment carries S, the joint class is the
 protocols that serve the family, the cost is at most the capacity, and a protocol of the class continues
 from a raw state.
reading: with the realization read as "the occupant's alignment as determined by the protocol", the typed
 content of B06 is what A2 gives at an interface with a nonempty task.
not_claimed: that B06 is redundant as an input. Its content sits in the hypotheses: that an interface with a
 nonempty task is there, hdet and hstart. hdet is the endpoint statement that the sibling seat showed does
 not follow from the eight declared forms. Nothing is claimed about the identification of B06's tasks with
 the raw distinctions of B02, B03 and B05.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_at_protocol_binding
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
    (carrierOf : {p // p ∈ protocols} → APFB01.PhysicalState Cont)
    (hdet : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}),
      APFB07a.Serves maintained sufficient usesToRealize S p →
        ∀ d ∈ S, d.val (carrierOf p) = true)
    (hstart : ∀ p : {p // p ∈ protocols},
      ∃ x : Raw, APFB01.physicalClass Cont x = carrierOf p ∧ Cont x p.val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, o.2.carrier = carrierOf (realized o.2.carried)) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by
  obtain ⟨⟨hserve, hC⟩, _⟩ := hA2 S
  have hC' : ((calibration (wholeResource (realized S)) : NNReal) : ℝ) ≤ ((C : NNReal) : ℝ) := hC
  obtain ⟨x, _, hx⟩ := hstart (realized S)
  refine ⟨{⟨(), ⟨carrierOf (realized S), S, fun d hd => hdet S (realized S) hserve d hd⟩⟩}, ?_,
    ⟨(), ⟨carrierOf (realized S), S, fun d hd => hdet S (realized S) hserve d hd⟩⟩,
    Set.mem_singleton _, hS, ?_, realized S, hserve, x, hx⟩
  · intro o' ho'
    rw [Set.mem_singleton_iff.mp ho']
  · refine le_trans (sInf_le ⟨realized S, hserve, rfl⟩) ?_
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
  (carrierOf :
    (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) →
      @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
  (hdet :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
      (p :
        @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
          @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
            (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p),
      @APFB07a.Serves.{apfNative_u_1, apfNative_u_2, apfNative_u_4}
          (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
          (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
            @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
              (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
          Record maintained sufficient usesToRealize S p →
        ∀ (d : @APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset),
          @Membership.mem.{apfNative_u_1, apfNative_u_1}
              (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
              (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
              (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1}
                (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
                (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                (@Finset.instSetLike.{apfNative_u_1}
                  (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)))
              S d →
            @Eq.{1} Bool
              (@Subtype.val.{apfNative_u_1 + 1}
                (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                (fun (d : @APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool) =>
                  @Membership.mem.{apfNative_u_1, apfNative_u_1}
                    (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool)
                    (Set.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    (@Set.instMembership.{apfNative_u_1}
                      (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                    Dset d)
                d (carrierOf p))
              Bool.true)
  (hstart :
    ∀
      (p :
        @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
          @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
            (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p),
      @Exists.{apfNative_u_1 + 1} Raw fun (x : Raw) =>
        And
          (@Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
            (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x) (carrierOf p))
          (Cont x
            (@Subtype.val.{apfNative_u_2 + 1} FullProcess
              (fun (p : FullProcess) =>
                @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                  (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
              p)))
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
          @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
            (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
              (@Sigma.snd.{0, apfNative_u_1} Unit
                (fun (x : Unit) => @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                o))
            (carrierOf
              (realized
                (@APFB06.OriginalAlignment.carried.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Sigma.snd.{0, apfNative_u_1} Unit
                    (fun (x : Unit) =>
                      @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                    o)))))
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
  exact @APFB06.amended_of_A2_at_protocol_binding
