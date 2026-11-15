-- Prove2me | solution 1 for APFB05.whole_gt_parts_of_shared_lt_floor
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T20:27:37.710412+00:00
-- url     : https://prove2.me/submissions/decf8ead-422c-4907-9ac4-d61c2b340896

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFB05_relation_residue
title: Holding a relation over two families costs at least the sum of their costs plus the floor less what they share
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:2746-2755 (marginal-floor lower bound on support-novel increments),
 1779-1781 (the residue kappa_int), 3046-3058 (the binary-form residue kappa_int(S1,S2)), 6481 (an
 irreducibly joint commitment requires substrate content beyond the union of the individual carriers),
 7313 (C4: linking costs extra). Codebank apf/delta_calculus.py: Delta = epsilon * (J - R), J the
 irreducibly joint terms and R the shared anchors; apf/yang_mills_md_bridge.py,
 check_T_contextuality_implies_superadditive_cost (a shared classical bit is subadditive, an irreducibly
 joint distinction superadditive). Def_APFPaper5_K1_SharedCost (seat 01WrrBvu): shared cost is the
 negative of the codebank's Delta on the two families. RULING_held_relation_reading_2026-11-13 (the
 relation is itself among the distinctions carried).
consumes_inputs: B05 (hB05) in the first three theorems. B05, B06 (hB06, at the extensional joint class on
 the physical domain) and B02 through its descent clause (hresp) in the fourth.
reading: hread in the fourth theorem is the adopted reading of B06's actualJoint (every actual joint
 alignment holds a relation among the distinctions it carries). It is not part of the Lean form of B06.
statement: (relation_residue_ge_floor_sub_shared) let r be tested and support-novel over S ∪ T, with S ∪ T
 and S ∪ T with r ledger-admissible. Then the cost of S ∪ T with r, less the cost of S and the cost of T,
 is at least the floor less the shared cost of S and T. (whole_gt_parts_of_shared_lt_floor) if S and T
 share less than the floor, the whole costs strictly more than the two parts together.
 (whole_ge_parts_add_floor_of_no_sharing) if S and T share nothing, the whole costs at least the two
 parts together plus the floor. (APFB06.held_relation_residue) under B05, B06 and the reading, some
 actual joint alignment holds a nonempty S and a relation r outside it such that, for every way of
 writing S as S1 ∪ S2, the cost of S with r, less the costs of S1 and S2, is at least the floor less the
 shared cost of S1 and S2.
not_claimed: any sign for the shared cost of the parts, so no sign for the residue: see
 Thm_APFB06_superadditivity_worlds, where it takes every sign. Any upper bound. That r is "the relation
 between" S and T in any sense beyond tested and support-novel over their union.
-/
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFPaper5_K1_SharedCost

import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source APFPaper5.K1

section
variable {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
  (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal)
  (maintained : (g : Context) → P g → Set (Record g))
  (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
  (tested : (g : Context) → D g → Prop)
  (C epsilon : Context → ℝ)

theorem APFB05.relation_residue_ge_floor_sub_shared
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S T : Finset (D g)) (r : D g) (htested : tested g r)
    (hU : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S ∪ T))
    (hW : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (S ∪ T)))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S ∪ T) r) :
    epsilon g - sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (insert r (S ∪ T)) -
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) S -
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) T := by
  have h := (hB05 g).2 (S ∪ T) r htested hU hW hnew
  unfold sharedCost
  linarith

theorem APFB05.whole_gt_parts_of_shared_lt_floor
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S T : Finset (D g)) (r : D g) (htested : tested g r)
    (hU : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S ∪ T))
    (hW : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert r (S ∪ T)))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S ∪ T) r)
    (hshare : sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T < epsilon g) :
    familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S +
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) T <
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r (S ∪ T)) := by
  have h := APFB05.relation_residue_ge_floor_sub_shared wholeResource calibration maintained
    sufficient usesToRealize tested C epsilon hB05 g S T r htested hU hW hnew
  linarith



end

namespace APFB06



end APFB06


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
  (g : Context) (S T : Finset.{apfNative_u_2} (D g)) (r : D g) (htested : tested g r)
  (hU :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Union.union.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)) (@Finset.instUnion.{apfNative_u_2} (D g) (inst g)) S
        T))
  (hW :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r
        (@Union.union.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)) (@Finset.instUnion.{apfNative_u_2} (D g) (inst g))
          S T)))
  (hnew :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Union.union.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)) (@Finset.instUnion.{apfNative_u_2} (D g) (inst g)) S
        T)
      r)
  (hshare :
    @LT.lt.{0} Real Real.instLT
      (@APFPaper5.K1.sharedCost.{apfNative_u_2} (D g) (inst g)
        (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
          (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g))
        S T)
      (epsilon g)),
  @LT.lt.{0} Real Real.instLT
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S)
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) T))
    (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) r
        (@Union.union.{apfNative_u_2} (Finset.{apfNative_u_2} (D g)) (@Finset.instUnion.{apfNative_u_2} (D g) (inst g))
          S T))) := by
  exact @APFB05.whole_gt_parts_of_shared_lt_floor
