-- Prove2me | solution 1 for APFB06.step_gives_alignment_of_same_family
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:16:33.962633+00:00
-- url     : https://prove2.me/submissions/2bc90b1d-3b91-49f4-8a33-4e6727b3c753

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB06_overlapping_families
title: Families may overlap: a protocol that serves a family serves the overlap, a step that keeps a family keeps the overlap and gives a new alignment of the same family, and with the bill a sum over the records kept the overlap is billed once
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement and question of 2026-11-13 17:30 HST ("The step acts on the full family and
 changes the alignment of the occupant. Can families overlap? I think so"). FOUNDATION_INPUTS B06 in declared
 form (a family is a finite set of tasks; no clause keeps two families apart). Def_APFB07a_ProtocolBinding.
 Thm_APFPaper5_K1_bill_is_a_sum. Earlier K1 drafts price the same overlap as shared cost (recordModel_sharedCost).
consumes_inputs: none as a declared predicate.
statement: (APFB07a.serves_of_subset, APFB07a.serves_inter) a protocol that serves a family serves every part
 of it, so it serves what the family shares with any other.
 (APFB07a.serves_union_iff) a protocol serves two families together exactly when it serves each.
 (APFB06.step_gives_alignment_of_same_family) hkeep says the step acts on the full family: after it every
 distinction of the family is still held. Then the state after the step carries an alignment with the same
 family, sitting at the object of that state. Same family, possibly a different carrier: the alignment has
 changed and the family has not.
 (APFB06.step_keeps_overlap) under hkeep, what the family shares with any other family is still held after
 the step.
 (APFPaper5.K1.bill_of_overlapping, overlap_billed_once) with the bill a sum over the records kept, the bill
 of two record sets together plus the bill of what they share is the sum of the two bills; with costs not
 negative, together is at most the sum.
reading: yes, families can overlap, and nothing typed forbids it. The overlap is held by either family's
 protocol, survives a step on either, and is paid for once.
not_claimed: hkeep (it is the author's statement that the step acts on the full family; the hold sentence
 at the level of the family); that the part of a second family outside the overlap is still held after a
 step of the first; whether a step changes which records two distinctions share.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding
import Theorems.Thm_APFPaper5_K1_hold_bills_nothing_more
import Theorems.Thm_APFPaper5_K1_bill_of_repeated_draw
import Theorems.Thm_APFPaper5_K1_repeated_draw_bounded

set_option autoImplicit false

theorem APFB07a.serves_of_subset {D P Record : Type*} (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S T : Finset D) (hTS : T ⊆ S) (p : P)
    (hp : APFB07a.Serves maintained sufficient usesToRealize S p) :
    APFB07a.Serves maintained sufficient usesToRealize T p :=
  fun d hd => hp d (hTS hd)

theorem APFB07a.serves_inter {D P Record : Type*} [DecidableEq D] (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S T : Finset D) (p : P) (hp : APFB07a.Serves maintained sufficient usesToRealize S p) :
    APFB07a.Serves maintained sufficient usesToRealize (S ∩ T) p :=
  APFB07a.serves_of_subset maintained sufficient usesToRealize S (S ∩ T)
    Finset.inter_subset_left p hp

theorem APFB07a.serves_union_iff {D P Record : Type*} [DecidableEq D] (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S T : Finset D) (p : P) :
    APFB07a.Serves maintained sufficient usesToRealize (S ∪ T) p ↔
      APFB07a.Serves maintained sufficient usesToRealize S p ∧
        APFB07a.Serves maintained sufficient usesToRealize T p := by
  constructor
  · intro h
    exact ⟨fun d hd => h d (Finset.mem_union_left T hd),
      fun d hd => h d (Finset.mem_union_right S hd)⟩
  · rintro ⟨hS, hT⟩ d hd
    rcases Finset.mem_union.mp hd with h | h
    · exact hS d h
    · exact hT d h

theorem APFB06.step_gives_alignment_of_same_family {Raw FullProcess : Type*}
    (Cont : Raw → FullProcess → Prop) (Dset : Set (APFB01.PhysicalState Cont → Bool))
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset)) (x : Raw)
    (u : FullProcess)
    (hkeep : ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true) :
    ∃ o : APFB06.OriginalAlignment Cont Dset,
      o.carried = S ∧ o.carrier = APFB01.physicalClass Cont (after x u) :=
  ⟨⟨APFB01.physicalClass Cont (after x u), S, hkeep⟩, rfl, rfl⟩

theorem APFB06.step_keeps_overlap {Raw FullProcess : Type*}
    (Cont : Raw → FullProcess → Prop) (Dset : Set (APFB01.PhysicalState Cont → Bool))
    [DecidableEq (APFB06.Task Cont Dset)]
    (after : Raw → FullProcess → Raw) (S T : Finset (APFB06.Task Cont Dset)) (x : Raw)
    (u : FullProcess)
    (hkeep : ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after x u)) = true) :
    ∀ d ∈ S ∩ T, d.val (APFB01.physicalClass Cont (after x u)) = true :=
  fun d hd => hkeep d (Finset.mem_inter.mp hd).1

namespace APFPaper5.K1

theorem bill_of_overlapping {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ) (K L : Finset Rec) :
    ∑ r ∈ K ∪ L, w r + ∑ r ∈ K ∩ L, w r = ∑ r ∈ K, w r + ∑ r ∈ L, w r :=
  Finset.sum_union_inter

theorem overlap_billed_once {Rec : Type*} [DecidableEq Rec] (w : Rec → ℝ)
    (hw : ∀ r : Rec, 0 ≤ w r) (K L : Finset Rec) :
    ∑ r ∈ K ∪ L, w r ≤ ∑ r ∈ K, w r + ∑ r ∈ L, w r := by
  have h := bill_of_overlapping w K L
  have h0 : 0 ≤ ∑ r ∈ K ∩ L, w r := Finset.sum_nonneg (fun r _ => hw r)
  linarith

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Raw : Type apfNative_u_1} {FullProcess : Type apfNative_u_2} (Cont : Raw → FullProcess → Prop)
  (Dset : Set.{apfNative_u_1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
  (after : Raw → FullProcess → Raw)
  (S : Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)) (x : Raw)
  (u : FullProcess)
  (hkeep :
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
                (Set.{apfNative_u_1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                (@Set.instMembership.{apfNative_u_1}
                  (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont → Bool))
                Dset d)
            d (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont (after x u)))
          Bool.true),
  @Exists.{apfNative_u_1 + 1} (@APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset)
    fun (o : @APFB06.OriginalAlignment.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset) =>
    And
      (@Eq.{apfNative_u_1 + 1}
        (Finset.{apfNative_u_1} (@APFB06.Task.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset))
        (@APFB06.OriginalAlignment.carried.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset o) S)
      (@Eq.{apfNative_u_1 + 1} (@APFB01.PhysicalState.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont)
        (@APFB06.OriginalAlignment.carrier.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont Dset o)
        (@APFB01.physicalClass.{apfNative_u_1, apfNative_u_2} Raw FullProcess Cont (after x u))) := by
  exact @APFB06.step_gives_alignment_of_same_family
