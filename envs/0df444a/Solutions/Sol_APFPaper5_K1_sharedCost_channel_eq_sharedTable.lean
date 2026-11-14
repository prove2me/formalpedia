-- Prove2me | solution 1 for APFPaper5.K1.sharedCost_channel_eq_sharedTable
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:55:42.030029+00:00
-- url     : https://prove2.me/submissions/00926b13-6210-49f3-95fd-d848dbd210ed

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_shared_cost_counting
title: In the counting model of the ledger's family cost, the shared cost of two families is the adopted shared-count score
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_SharedCost and Def_APFPaper5_K1_SharedCount. The worked model asked for by ruling 4
 of the eight decisions of 2026-11-12.
consumes_inputs: none. A MODEL of the source vocabulary: a protocol is the finite set of records it maintains,
 its bill is the number of those records, and a distinction is served when its own records are maintained.
statement: (familyCost_counting) in this model the family cost of S is the number of records the members of S
 need between them. (sharedCost_counting_eq_sharedTable) for that cost the shared cost of two single families
 is sharedTable. (adopted_score_is_ledger_shared_cost) so the adopted score is the shared cost of the ledger's
 familyCost in the counting model. (sharedCost_channel_eq_sharedTable) with cost the floor times the channel
 count and no joint channel, the table of shared costs of a list of families is the floor times sharedTable
 of their channel sets.
not_claimed: that any interface is the counting model; that bills count records in general.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_sharedTable_eq_card
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v w
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem familyCost_counting (fam : ι → Finset Rec) (S : Finset ι) :
    familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => (r.card : NNReal)) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S =
      ((S.biUnion fam).card : ℝ) := by
  unfold familyCost
  apply IsLeast.csInf_eq
  refine ⟨⟨S.biUnion fam, fun d hd => ⟨↑(S.biUnion fam), subset_rfl, ?_, trivial⟩, ?_⟩, ?_⟩
  · exact Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem fam hd)
  · simp
  · rintro c ⟨p, hp, rfl⟩
    have hsub : S.biUnion fam ⊆ p := by
      intro r hr
      obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨sigma, hsig, hsuf, _⟩ := hp d hd
      exact Finset.mem_coe.mp (hsig (hsuf (Finset.mem_coe.mpr hrd)))
    have hc : (S.biUnion fam).card ≤ p.card := Finset.card_le_card hsub
    have hr : ((S.biUnion fam).card : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast hc
    simpa using hr

theorem sharedCost_counting_eq_sharedTable [Fintype Rec] [DecidableEq ι] (fam : ι → Finset Rec)
    (i j : ι) :
    sharedCost (fun S : Finset ι => ((S.biUnion fam).card : ℝ)) {i} {j} = sharedTable fam i j := by
  rw [sharedTable_eq_card]
  simp only [sharedCost, Finset.union_biUnion, Finset.singleton_biUnion]
  have h := Finset.card_union_add_card_inter (fam i) (fam j)
  have h' : ((fam i ∪ fam j).card : ℝ) + ((fam i ∩ fam j).card : ℝ) =
      ((fam i).card : ℝ) + ((fam j).card : ℝ) := by exact_mod_cast h
  linarith

theorem adopted_score_is_ledger_shared_cost [Fintype Rec] [DecidableEq ι] (fam : ι → Finset Rec)
    (i j : ι) :
    sharedCost (familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => (r.card : NNReal)) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True)) {i} {j} =
      sharedTable fam i j := by
  have hfun : (familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => (r.card : NNReal)) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True)) =
      fun S : Finset ι => ((S.biUnion fam).card : ℝ) := funext (familyCost_counting fam)
  rw [hfun]
  exact sharedCost_counting_eq_sharedTable fam i j

theorem sharedCost_channel_eq_sharedTable {D : Type u} [DecidableEq D] {Ch : Type v} [Fintype Ch]
    [DecidableEq Ch] {κ : Type w} (chan : Finset D → Finset Ch) (eps : ℝ) (fams : κ → Finset D)
    (hJ : ∀ a b, chan (fams a ∪ fams b) = chan (fams a) ∪ chan (fams b)) (a b : κ) :
    sharedCost (fun X => eps * ((chan X).card : ℝ)) (fams a) (fams b) =
      eps * sharedTable (fun k => chan (fams k)) a b := by
  rw [sharedCost_channel_no_joint chan eps _ _ (hJ a b), sharedTable_eq_card]

end APFPaper5.K1


universe apfNative_u apfNative_v apfNative_w
theorem solution :
∀ {D : Type apfNative_u} [inst : DecidableEq.{apfNative_u + 1} D] {Ch : Type apfNative_v}
  [inst_1 : Fintype.{apfNative_v} Ch] [inst_2 : DecidableEq.{apfNative_v + 1} Ch] {κ : Type apfNative_w}
  (chan : Finset.{apfNative_u} D → Finset.{apfNative_v} Ch) (eps : Real) (fams : κ → Finset.{apfNative_u} D)
  (hJ :
    ∀ (a b : κ),
      @Eq.{apfNative_v + 1} (Finset.{apfNative_v} Ch)
        (chan
          (@Union.union.{apfNative_u} (Finset.{apfNative_u} D) (@Finset.instUnion.{apfNative_u} D inst) (fams a)
            (fams b)))
        (@Union.union.{apfNative_v} (Finset.{apfNative_v} Ch) (@Finset.instUnion.{apfNative_v} Ch inst_2)
          (chan (fams a)) (chan (fams b))))
  (a b : κ),
  @Eq.{1} Real
    (@APFPaper5.K1.sharedCost.{apfNative_u} D inst
      (fun (X : Finset.{apfNative_u} D) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{apfNative_v} Ch (chan X))))
      (fams a) (fams b))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
      (@APFPaper5.K1.sharedTable.{apfNative_w, apfNative_v} κ Ch inst_1 inst_2 (fun (k : κ) => chan (fams k)) a b)) := by
  exact @APFPaper5.K1.sharedCost_channel_eq_sharedTable
