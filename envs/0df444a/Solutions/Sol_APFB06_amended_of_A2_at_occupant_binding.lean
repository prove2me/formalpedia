-- Prove2me | solution 1 for APFB06.amended_of_A2_at_occupant_binding
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:56:43.539636+00:00
-- url     : https://prove2.me/submissions/4ef8065a-5219-452d-a285-d64f92dbc84e

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB06_occupancy_at_occupant_binding
title: At the occupant binding, A2 alone says the selected protocol is admitted at every occupant, and gives B06's declared form at any occupant with a nonempty family
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFB07a_OccupantBinding. The author's direction of 2026-11-13 16:33 HST ("You can derive all the
 of the open items"). FOUNDATION_INPUTS B06 and B07a in declared form.
consumes_inputs: A2 (APFB07a.A2Selection) in declared form, at the occupant binding. B06's declared form is
 the CONCLUSION of the second theorem. The formal fidelity of A2 is NOT CERTIFIED.
statement: an interface is an alignment with a raw state of its carrier.
 (APFB07a.realized_admitted_at_occupant) at every interface the protocol A2 selects is admitted at the
 occupant's raw state, serves its whole family and is in budget. This is the admissibility half of A2's
 declared form read at the binding; nothing else is assumed.
 (APFB06.amended_of_A2_at_occupant_binding) at any interface whose family is nonempty, the amended B06 holds
 at the extensional joint class with that alignment as the actual one.
reading: the hypotheses of passes 25 to 27 (hdet, hstart, hocc, hinst) are not needed here. That the
 selected protocol starts at the occupant, and that it is admitted somewhere, are what A2 says once its
 domain is the occupant's continuation class. "Taken again" is the first theorem at the next occupant.
not_claimed: that the source's admissible domain is this binding (put to the author); that the state after a
 step is an occupant of the same family (the hold sentence); that B06 is redundant, since the existence of
 an occupant with a nonempty family is its content.
-/
import Definitions.Def_APFB07a_OccupantBinding

set_option autoImplicit false

theorem APFB07a.realized_admitted_at_occupant
    {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : NNReal)
    (realized : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier} → {p // p ∈ protocols})
    (hA2 : APFB07a.A2Selection
      (Interface := {ox : APFB06.OriginalAlignment Cont Dset × Raw //
        APFB01.physicalClass Cont ox.2 = ox.1.carrier})
      (Configuration := fun _ => {p // p ∈ protocols})
      (fun i p => APFB07a.occupantAdmissible Cont Dset protocols wholeResource calibration
        maintained sufficient usesToRealize (C : ℝ) i.val.1 i.val.2 p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (i : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier}) :
    Cont i.val.2 (realized i).val ∧
      APFB07a.Serves maintained sufficient usesToRealize i.val.1.carried (realized i) ∧
      APFB07a.protocolBill wholeResource calibration (realized i) ≤ (C : ℝ) :=
  (hA2 i).1

theorem APFB06.amended_of_A2_at_occupant_binding
    {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : NNReal)
    (realized : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier} → {p // p ∈ protocols})
    (hA2 : APFB07a.A2Selection
      (Interface := {ox : APFB06.OriginalAlignment Cont Dset × Raw //
        APFB01.physicalClass Cont ox.2 = ox.1.carrier})
      (Configuration := fun _ => {p // p ∈ protocols})
      (fun i p => APFB07a.occupantAdmissible Cont Dset protocols wholeResource calibration
        maintained sufficient usesToRealize (C : ℝ) i.val.1 i.val.2 p)
      (fun _ p => APFB07a.protocolBill wholeResource calibration p) realized)
    (i : {ox : APFB06.OriginalAlignment Cont Dset × Raw //
      APFB01.physicalClass Cont ox.2 = ox.1.carrier})
    (hS : i.val.1.carried.Nonempty) :
    APFB06.AmendedB06_20260914 (Context := Unit) (Raw := fun _ => Raw)
      (FullProcess := fun _ => FullProcess) (Resource := fun _ => Resource)
      (fun _ => Cont) (fun _ => Dset) (fun _ => protocols)
      (fun _ T => {p | APFB07a.Serves maintained sufficient usesToRealize T p})
      (fun _ => wholeResource) (fun _ => calibration) (fun _ => C)
      ({⟨(), i.val.1⟩} : Set (Sigma fun _ : Unit => APFB06.OriginalAlignment Cont Dset)) := by
  obtain ⟨hcont, hserve, hC⟩ := (hA2 i).1
  have hC' : ((calibration (wholeResource (realized i)) : NNReal) : ℝ) ≤ ((C : NNReal) : ℝ) := hC
  refine ⟨⟨(), i.val.1⟩, Set.mem_singleton _, hS, ?_, realized i, hserve, i.val.2, hcont⟩
  refine le_trans (sInf_le ⟨realized i, hserve, rfl⟩) ?_
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
    (@Subtype.{apfNative_u_1 + 1}
        (Prod.{apfNative_u_1, apfNative_u_1}
          (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
        fun
          (ox :
            Prod.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
        @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
          (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
            (@Prod.snd.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
          (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
            (@Prod.fst.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))) →
      @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
        @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
          (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, apfNative_u_2}
      (@Subtype.{apfNative_u_1 + 1}
        (Prod.{apfNative_u_1, apfNative_u_1}
          (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
        fun
          (ox :
            Prod.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
        @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
          (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
            (@Prod.snd.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
          (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
            (@Prod.fst.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
      (fun
          (x :
            @Subtype.{apfNative_u_1 + 1}
              (Prod.{apfNative_u_1, apfNative_u_1}
                (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
              fun
                (ox :
                  Prod.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
              @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))) =>
        @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
          @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
            (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p)
      (fun
          (i :
            @Subtype.{apfNative_u_1 + 1}
              (Prod.{apfNative_u_1, apfNative_u_1}
                (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
              fun
                (ox :
                  Prod.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
              @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
          (p :
            @Subtype.{apfNative_u_2 + 1} FullProcess fun (p : FullProcess) =>
              @Membership.mem.{apfNative_u_2, apfNative_u_2} FullProcess (Set.{apfNative_u_2} FullProcess)
                (@Set.instMembership.{apfNative_u_2} FullProcess) protocols p) =>
        @APFB07a.occupantAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Raw FullProcess
          Resource Record Cont Dset protocols wholeResource calibration maintained sufficient usesToRealize
          (NNReal.toReal C)
          (@Prod.fst.{apfNative_u_1, apfNative_u_1}
            (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw
            (@Subtype.val.{apfNative_u_1 + 1}
              (Prod.{apfNative_u_1, apfNative_u_1}
                (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
              (fun
                  (ox :
                    Prod.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
                @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                  (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                    (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                  (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                    (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
              i))
          (@Prod.snd.{apfNative_u_1, apfNative_u_1}
            (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw
            (@Subtype.val.{apfNative_u_1 + 1}
              (Prod.{apfNative_u_1, apfNative_u_1}
                (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
              (fun
                  (ox :
                    Prod.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
                @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                  (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                    (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                  (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                    (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                      (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
              i))
          p)
      (fun
          (x :
            @Subtype.{apfNative_u_1 + 1}
              (Prod.{apfNative_u_1, apfNative_u_1}
                (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
              fun
                (ox :
                  Prod.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
              @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
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
  (i :
    @Subtype.{apfNative_u_1 + 1}
      (Prod.{apfNative_u_1, apfNative_u_1}
        (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
      fun
        (ox :
          Prod.{apfNative_u_1, apfNative_u_1}
            (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
      @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
        (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
          (@Prod.snd.{apfNative_u_1, apfNative_u_1}
            (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
        (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
          (@Prod.fst.{apfNative_u_1, apfNative_u_1}
            (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
  (hS :
    @Finset.Nonempty.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
      (@APFB06.OriginalAlignment.carried.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
        (@Prod.fst.{apfNative_u_1, apfNative_u_1}
          (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw
          (@Subtype.val.{apfNative_u_1 + 1}
            (Prod.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
            (fun
                (ox :
                  Prod.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
              @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
            i)))),
  @APFB06.AmendedB06_20260914.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3} Unit (fun (x : Unit) => Raw)
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
    (fun (x : Unit) => wholeResource) (fun (x : Unit) => calibration) (fun (x : Unit) => C)
    (@Singleton.singleton.{apfNative_u_1, apfNative_u_1}
      (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
        @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
      (Set.{apfNative_u_1}
        (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
          @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
      (@Set.instSingletonSet.{apfNative_u_1}
        (@Sigma.{0, apfNative_u_1} Unit fun (x : Unit) =>
          @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
      (@Sigma.mk.{0, apfNative_u_1} Unit
        (fun (x : Unit) => @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Unit.unit
        (@Prod.fst.{apfNative_u_1, apfNative_u_1}
          (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw
          (@Subtype.val.{apfNative_u_1 + 1}
            (Prod.{apfNative_u_1, apfNative_u_1}
              (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw)
            (fun
                (ox :
                  Prod.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw) =>
              @Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
                (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont
                  (@Prod.snd.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox))
                (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset
                  (@Prod.fst.{apfNative_u_1, apfNative_u_1}
                    (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) Raw ox)))
            i)))) := by
  exact @APFB06.amended_of_A2_at_occupant_binding
