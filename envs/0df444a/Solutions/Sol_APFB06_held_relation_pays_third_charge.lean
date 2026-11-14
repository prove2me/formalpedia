-- Prove2me | solution 1 for APFB06.held_relation_pays_third_charge
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:17:51.941544+00:00
-- url     : https://prove2.me/submissions/5ea91d07-a89d-425c-bc9f-2b059c39f949

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB06_held_relation_third_charge
title: Under the proposed reading of B06, an actual held family pays a third charge
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFB06_HeldRelation.
consumes_inputs: B05 (hB05). B06 only in its PROPOSED reading (hrel : HeldRelationExists), which is not yet the
 declared input's Lean form.
statement: under B05 and the proposed reading, there are a context, a nonempty family S and a task r outside S
 with familyCost S + epsilon <= familyCost (insert r S), hence familyCost S < familyCost (insert r S).
not_claimed: any premium over separately realized singleton costs; any disturbance that defeats the pair.
-/
import Definitions.Def_APFB06_HeldRelation
import Theorems.Thm_APFB05_relation_strictly_dearer
import Theorems.Thm_APFB05_no_free_rider

set_option autoImplicit false
open APFPaper1.Source

theorem APFB06.held_relation_pays_third_charge
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (hrel : APFB06.HeldRelationExists wholeResource calibration maintained sufficient usesToRealize
      tested C) :
    ∃ (g : Context) (S : Finset (D g)) (r : D g), S.Nonempty ∧ r ∉ S ∧
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + epsilon g ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) ∧
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S <
        familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by
  obtain ⟨g, S, r, hne, hr, ht, hS, hSr, hnew⟩ := hrel
  exact ⟨g, S, r, hne, hr,
    APFB05.relation_task_third_charge wholeResource calibration maintained sufficient
      usesToRealize tested C epsilon hB05 g S r ht hS hSr hnew,
    APFB05.relation_strictly_dearer wholeResource calibration maintained sufficient
      usesToRealize tested C epsilon hB05 g S r ht hS hSr hnew⟩


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
  (hrel :
    @APFB06.HeldRelationExists.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R
      Record inst wholeResource calibration maintained sufficient usesToRealize tested C),
  @Exists.{apfNative_u_1 + 1} Context fun (g : Context) =>
    @Exists.{apfNative_u_2 + 1} (Finset.{apfNative_u_2} (D g)) fun (S : Finset.{apfNative_u_2} (D g)) =>
      @Exists.{apfNative_u_2 + 1} (D g) fun (r : D g) =>
        And (@Finset.Nonempty.{apfNative_u_2} (D g) S)
          (And
            (Not
              (@Membership.mem.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
                (@SetLike.instMembership.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} (D g)) (D g)
                  (@Finset.instSetLike.{apfNative_u_2} (D g)))
                S r))
            (And
              (@LE.le.{0} Real Real.instLE
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g)
                    (R g) (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
                    S)
                  (epsilon g))
                (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g)
                  (R g) (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
                  (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
                    (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r S)))
              (@LT.lt.{0} Real Real.instLT
                (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g)
                  (R g) (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S)
                (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g)
                  (R g) (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
                  (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
                    (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r S))))) := by
  exact @APFB06.held_relation_pays_third_charge
