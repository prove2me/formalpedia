-- Prove2me | solution 1 for APFB05.cross_score_le_own_sub_floor
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:48:11.503873+00:00
-- url     : https://prove2.me/submissions/d4de1c7b-27ff-47a5-9b42-06a3af7f2c50

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB05_shared_cost_floor
title: On the ledger the shared cost is capped by each family's own cost, a new distinction scores at least the floor against itself, and strictly less against a family it is new to
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_SharedCost; FOUNDATION_INPUTS B05 (MarginalFloor, as designated).
consumes_inputs: B05, as a hypothesis, in the three theorems named APFB05. The first theorem consumes none.
statement: (sharedCost_familyCost_le) if the union is feasible, the shared cost of S and T is at most the cost
 of S and at most the cost of T. (APFB05.self_score_ge_floor) a tested distinction that is support-novel over
 the empty family, with both families admissible, has shared cost with itself at least the floor.
 (APFB05.cross_score_le_own_sub_floor) a tested distinction e that is support-novel over an admissible family
 S, with insert e S admissible, has shared cost with S at most its own cost less the floor.
 (APFB05.cross_score_lt_self_score) so that shared cost is strictly below e's shared cost with itself.
not_claimed: that the shared cost is nonnegative; any bound from below; that the table of shared costs is a
 nonnegative form on combinations; K1.
-/
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
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

theorem APFPaper5.K1.sharedCost_familyCost_le (g : Context) (S T : Finset (D g))
    (hfeas : familyFeasible (maintained g) (sufficient g) (usesToRealize g) (S ∪ T)) :
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S ∧
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S T ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) T :=
  ⟨sharedCost_le_left _ S T (familyCost_mono (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) Finset.subset_union_right hfeas),
   sharedCost_le_right _ S T (familyCost_mono (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) Finset.subset_union_left hfeas)⟩

theorem APFB05.self_score_ge_floor
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (d : D g) (htested : tested g d)
    (h0 : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) ∅)
    (hd : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d ∅))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) ∅ d) :
    epsilon g ≤ sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g)) (insert d ∅) (insert d ∅) := by
  rw [sharedCost_self]
  have h := (hB05 g).2 ∅ d htested h0 hd hnew
  have hnn := familyCost_nonneg (wholeResource g) (calibration g) (maintained g)
    (sufficient g) (usesToRealize g) (∅ : Finset (D g))
  linarith

theorem APFB05.cross_score_le_own_sub_floor
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (e : D g) (htested : tested g e)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSe : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert e S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S e) :
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S {e} ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) {e} - epsilon g := by
  have h := (hB05 g).2 S e htested hS hSe hnew
  have hU : S ∪ {e} = insert e S := by rw [Finset.union_comm, ← Finset.insert_eq]
  unfold sharedCost
  rw [hU]
  linarith

theorem APFB05.cross_score_lt_self_score
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (g : Context) (S : Finset (D g)) (e : D g) (htested : tested g e)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hSe : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert e S))
    (hnew : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S e) :
    sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) S {e} <
      sharedCost (familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g)) {e} {e} := by
  rw [sharedCost_self]
  have h := APFB05.cross_score_le_own_sub_floor wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g S e htested hS hSe hnew
  have heps := (hB05 g).1
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
  (g : Context) (S : Finset.{apfNative_u_2} (D g)) (e : D g) (htested : tested g e)
  (hS :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g) S)
  (hSe :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) e S))
  (hnew :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S e),
  @LE.le.{0} Real Real.instLE
    (@APFPaper5.K1.sharedCost.{apfNative_u_2} (D g) (inst g)
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g))
      S
      (@Singleton.singleton.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instSingleton.{apfNative_u_2} (D g)) e))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
        (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g)
        (@Singleton.singleton.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
          (@Finset.instSingleton.{apfNative_u_2} (D g)) e))
      (epsilon g)) := by
  exact @APFB05.cross_score_le_own_sub_floor
