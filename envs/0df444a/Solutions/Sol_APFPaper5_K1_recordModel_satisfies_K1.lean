-- Prove2me | solution 1 for APFPaper5.K1.recordModel_satisfies_K1
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:11:55.215136+00:00
-- url     : https://prove2.me/submissions/cb06740c-081d-4333-85e7-a4e7879e10f8

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_weighted_record_model
title: In the weighted record model the family cost is the weight of the records needed, the shared cost is the weight of the shared records, and K1's record-book conditions hold
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_RecordModel and Def_APFPaper5_K1_SharedCost.
consumes_inputs: none. Theorems about a MODEL of the source vocabulary.
statement: (familyCost_weighted, recordModelCost_eq) the family cost of S is the total cost of the records its
 members need. (atomTable_eq_sum_inter) the atom table of membership marks is the weight of shared records.
 (sharedCost_weighted_eq_atomTable, recordModel_sharedCost) the shared cost of two single families is that
 atom table. (recordModel_satisfies_K1) if every family has a record of positive cost that no other family
 needs, the table of shared costs is bilinear with a faithful nonnegative diagonal.
 Record costs need not be equal: no clause says cost depends only on the number of records.
not_claimed: that any interface is a record model; the boundary-role isomorphism beyond the identity map; K1.
-/
import Definitions.Def_APFPaper5_K1_RecordModel
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]

theorem familyCost_weighted (w : Rec → NNReal) (fam : ι → Finset Rec) (S : Finset ι) :
    familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S =
      ∑ a ∈ S.biUnion fam, (w a : ℝ) := by
  unfold familyCost
  apply IsLeast.csInf_eq
  refine ⟨⟨S.biUnion fam, fun d hd => ⟨↑(S.biUnion fam), subset_rfl, ?_, trivial⟩, ?_⟩, ?_⟩
  · exact Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem fam hd)
  · exact NNReal.coe_sum _ _
  · rintro c ⟨p, hp, rfl⟩
    have hsub : S.biUnion fam ⊆ p := by
      intro r hr
      obtain ⟨d, hd, hrd⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨sigma, hsig, hsuf, _⟩ := hp d hd
      exact Finset.mem_coe.mp (hsig (hsuf (Finset.mem_coe.mpr hrd)))
    have hle : ∑ a ∈ S.biUnion fam, (w a : ℝ) ≤ ∑ a ∈ p, (w a : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => NNReal.coe_nonneg _)
    have hc : ((∑ a ∈ p, w a : NNReal) : ℝ) = ∑ a ∈ p, (w a : ℝ) := NNReal.coe_sum _ _
    show ∑ a ∈ S.biUnion fam, (w a : ℝ) ≤ ((∑ a ∈ p, w a : NNReal) : ℝ)
    rw [hc]
    exact hle

theorem recordModelCost_eq (w : Rec → NNReal) (fam : ι → Finset Rec) (S : Finset ι) :
    recordModelCost w fam S = ∑ a ∈ S.biUnion fam, (w a : ℝ) :=
  familyCost_weighted w fam S

theorem atomTable_eq_sum_inter [Fintype Rec] (w : Rec → ℝ) (fam : ι → Finset Rec) (i j : ι) :
    atomTable w (fun k a => decide (a ∈ fam k)) i j = ∑ a ∈ fam i ∩ fam j, w a := by
  have hterm : ∀ a : Rec, w a * (ind (decide (a ∈ fam i)) * ind (decide (a ∈ fam j))) =
      if a ∈ fam i ∩ fam j then w a else 0 := by
    intro a
    by_cases h1 : a ∈ fam i <;> by_cases h2 : a ∈ fam j <;> simp [ind, Finset.mem_inter, h1, h2]
  unfold atomTable
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem sharedCost_weighted_eq_atomTable [Fintype Rec] [DecidableEq ι] (w : Rec → ℝ)
    (fam : ι → Finset Rec) (i j : ι) :
    sharedCost (fun S : Finset ι => ∑ a ∈ S.biUnion fam, w a) {i} {j} =
      atomTable w (fun k a => decide (a ∈ fam k)) i j := by
  rw [atomTable_eq_sum_inter]
  simp only [sharedCost, Finset.union_biUnion, Finset.singleton_biUnion]
  have h : ∑ x ∈ fam i ∪ fam j, w x + ∑ x ∈ fam i ∩ fam j, w x =
      ∑ x ∈ fam i, w x + ∑ x ∈ fam j, w x := Finset.sum_union_inter
  linarith

theorem recordModel_sharedCost [Fintype Rec] [DecidableEq ι] (w : Rec → NNReal)
    (fam : ι → Finset Rec) (i j : ι) :
    sharedCost (recordModelCost w fam) {i} {j} =
      atomTable (fun a => (w a : ℝ)) (fun k a => decide (a ∈ fam k)) i j := by
  have hfun : recordModelCost w fam = fun S : Finset ι => ∑ a ∈ S.biUnion fam, (w a : ℝ) :=
    funext (recordModelCost_eq w fam)
  rw [hfun]
  exact sharedCost_weighted_eq_atomTable (fun a => (w a : ℝ)) fam i j

theorem recordModel_satisfies_K1 [Fintype Rec] [Fintype ι] [DecidableEq ι] (w : Rec → NNReal)
    (fam : ι → Finset Rec) (hprivate : ∀ i, ∃ a, 0 < w a ∧ ∀ j, (a ∈ fam j ↔ j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j => sharedCost (recordModelCost w fam) {i} {j})) ∧
      FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost (recordModelCost w fam) {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have htab : (fun i j => sharedCost (recordModelCost w fam) {i} {j}) =
      atomTable (fun a => (w a : ℝ)) (fun k a => decide (a ∈ fam k)) := by
    funext i j
    exact recordModel_sharedCost w fam i j
  rw [htab]
  refine record_book_table_satisfies_K1 _ (fun a => NNReal.coe_nonneg _) _ (fun i => ?_)
  obtain ⟨a, hpos, ha⟩ := hprivate i
  exact ⟨a, NNReal.coe_pos.mpr hpos, fun j => decide_eq_decide.mpr (ha j)⟩

end APFPaper5.K1


universe apfNative_u apfNative_v
theorem solution :
∀ {ι : Type apfNative_u} {Rec : Type apfNative_v} [DecidableEq.{apfNative_v + 1} Rec] [Fintype.{apfNative_v} Rec]
  [inst : Fintype.{apfNative_u} ι] [inst_1 : DecidableEq.{apfNative_u + 1} ι] (w : Rec → NNReal)
  (fam : ι → Finset.{apfNative_v} Rec)
  (hprivate :
    ∀ (i : ι),
      @Exists.{apfNative_v + 1} Rec fun (a : Rec) =>
        And
          (@LT.lt.{0} NNReal (@Preorder.toLT.{0} NNReal (@PartialOrder.toPreorder.{0} NNReal NNReal.instPartialOrder))
            (@OfNat.ofNat.{0} NNReal (nat_lit 0) (@Zero.toOfNat0.{0} NNReal NNReal.instZero)) (w a))
          (∀ (j : ι),
            Iff
              (@Membership.mem.{apfNative_v, apfNative_v} Rec (Finset.{apfNative_v} Rec)
                (@SetLike.instMembership.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec
                  (@Finset.instSetLike.{apfNative_v} Rec))
                (fam j) a)
              (@Eq.{apfNative_u + 1} ι j i))),
  And
    (@APFPaper5.K1.IsBilinear.{apfNative_u, apfNative_u} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u} ι inst fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{apfNative_u} ι inst_1
          (@APFPaper5.K1.recordModelCost.{apfNative_u, apfNative_v} ι Rec w fam)
          (@Singleton.singleton.{apfNative_u, apfNative_u} ι (Finset.{apfNative_u} ι)
            (@Finset.instSingleton.{apfNative_u} ι) i)
          (@Singleton.singleton.{apfNative_u, apfNative_u} ι (Finset.{apfNative_u} ι)
            (@Finset.instSingleton.{apfNative_u} ι) j)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{apfNative_u, apfNative_u} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{apfNative_u} ι inst fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{apfNative_u} ι inst_1
          (@APFPaper5.K1.recordModelCost.{apfNative_u, apfNative_v} ι Rec w fam)
          (@Singleton.singleton.{apfNative_u, apfNative_u} ι (Finset.{apfNative_u} ι)
            (@Finset.instSingleton.{apfNative_u} ι) i)
          (@Singleton.singleton.{apfNative_u, apfNative_u} ι (Finset.{apfNative_u} ι)
            (@Finset.instSingleton.{apfNative_u} ι) j))
      (@LinearEquiv.refl.{0, apfNative_u} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{apfNative_u, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.recordModel_satisfies_K1
