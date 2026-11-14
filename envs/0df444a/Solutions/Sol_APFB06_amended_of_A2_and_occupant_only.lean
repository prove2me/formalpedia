-- Prove2me | solution 1 for APFB06.amended_of_A2_and_occupant_only
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:42.510628+00:00
-- url     : https://prove2.me/submissions/1fc7d90a-bbcb-46d6-af39-bd6d8faabdf0

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB06_protocols_only_at_occupants
title: If a protocol that serves a family is admitted only at states that hold the family, then A2 at the protocol binding gives B06's declared form with the occupant found, not supplied; and wherever the protocol can be taken again the family is still held
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-13 16:23 HST ("Protocols can only be instantiated or held by the
 occupant"). FOUNDATION_INPUTS B06 and B07a in declared form. Def_APFB07a_ProtocolBinding.
 Thm_APFB06_occupant_alignment_holds, whose hypothesis hstart this node replaces.
consumes_inputs: A2 in declared form at the protocol binding, in the first theorem; B06's declared form is
 its CONCLUSION. The formal fidelity of A2 is NOT CERTIFIED.
statement: hocc is the author's statement in ledger terms: if a protocol serves a family and is admitted at
 a raw state, the physical object of that state holds every distinction of the family.
 (APFB06.amended_of_A2_and_occupant_only) A2 at the protocol binding; hocc; and for each family the realized
 protocol is admitted at some raw state (hinst). Then for every nonempty task family the amended B06 holds
 at the extensional joint class, with the actual alignment sitting at the object of a raw state where the
 realized protocol is admitted. The occupant is found from the protocol; no occupant map is supplied and
 nothing says in advance where the protocol starts.
 (APFB06.family_still_held_where_protocol_goes_on) under hocc, if after a process the protocol is admitted
 again, the state after it still holds every distinction of the family.
reading: "starts at the occupant" follows from the author's statement. "Still drawn afterward" follows from
 it together with "can be taken again".
not_claimed: hocc itself (in World U the protocol word is admitted at a state that is not the occupant:
 APFPaper5.Worlds.world_U_hold_not_undone); that the realized protocol is admitted anywhere (hinst); that it
 can be taken again; any identification of B06's tasks with the raw distinctions of B02, B03 and B05.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false

theorem APFB06.amended_of_A2_and_occupant_only
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
    (hocc : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}) (x : Raw),
      APFB07a.Serves maintained sufficient usesToRealize S p → Cont x p.val →
        ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (hinst : ∀ S : Finset (APFB06.Task Cont Dset), ∃ x : Raw, Cont x (realized S).val)
    (S : Finset (APFB06.Task Cont Dset)) (hS : S.Nonempty) :
    ∃ actualJoint : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset),
      (∀ o ∈ actualJoint, ∃ x : Raw, o.2.carrier = APFB01.physicalClass Cont x ∧
        Cont x (realized o.2.carried).val) ∧
      APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
        (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
        (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
        (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
        (fun _ => wholeResource) (fun _ => calibration) (fun _ => C) actualJoint := by
  obtain ⟨⟨hserve, hC⟩, _⟩ := hA2 S
  have hC' : ((calibration (wholeResource (realized S)) : NNReal) : ℝ) ≤ ((C : NNReal) : ℝ) := hC
  obtain ⟨x, hx⟩ := hinst S
  refine ⟨{⟨(), ⟨APFB01.physicalClass Cont x, S, hocc S (realized S) x hserve hx⟩⟩}, ?_,
    ⟨(), ⟨APFB01.physicalClass Cont x, S, hocc S (realized S) x hserve hx⟩⟩,
    Set.mem_singleton _, hS, ?_, realized S, hserve, x, hx⟩
  · intro o' ho'
    rw [Set.mem_singleton_iff.mp ho']
    exact ⟨x, rfl, hx⟩
  · refine le_trans (sInf_le ⟨realized S, hserve, rfl⟩) ?_
    exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hC')

theorem APFB06.family_still_held_where_protocol_goes_on
    {Raw FullProcess Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (hocc : ∀ (S : Finset (APFB06.Task Cont Dset)) (p : {p // p ∈ protocols}) (x : Raw),
      APFB07a.Serves maintained sufficient usesToRealize S p → Cont x p.val →
        ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset))
    (p : {p // p ∈ protocols}) (hp : APFB07a.Serves maintained sufficient usesToRealize S p)
    (x : Raw) (u : FullProcess) (hagain : Cont (after x u) p.val) :
    ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true :=
  hocc S p (after x u) hp hagain


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
  (hocc :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
      (p :
        @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
          @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
            (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
      (x : Raw),
      @APFB07a.Serves.{apfNative_u_1, apfNative_u_2, apfNative_u_4}
          (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
          (@Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
            @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
              (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
          Record maintained sufficient usesToRealize S p →
        Cont x
            (@Subtype.val.{apfNative_u_2 + 1} FullProcess
              (fun (p : FullProcess) =>
                @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                  (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
              p) →
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
                  d (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x))
                Bool.true)
  (hinst :
    ∀ (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)),
      @Exists.{apfNative_u_1 + 1} Raw fun (x : Raw) =>
        Cont x
          (@Subtype.val.{apfNative_u_2 + 1} FullProcess
            (fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
            (realized S)))
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
          @Exists.{apfNative_u_1 + 1} Raw fun (x : Raw) =>
            And
              (@Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Sigma.snd.{0, apfNative_u_1} Unit
                    (fun (x : Unit) =>
                      @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                    o))
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont x))
              (Cont x
                (@Subtype.val.{apfNative_u_2 + 1} FullProcess
                  (fun (p : FullProcess) =>
                    @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                      (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
                  (realized
                    (@APFB06.OriginalAlignment.carried.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                      (@Sigma.snd.{0, apfNative_u_1} Unit
                        (fun (x : Unit) =>
                          @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
                        o))))))
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
  exact @APFB06.amended_of_A2_and_occupant_only
