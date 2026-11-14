-- Prove2me | solution 1 for APFB05.weighted_record_model_satisfies_floor
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:15:57.676721+00:00
-- url     : https://prove2.me/submissions/283240d1-32e1-49f4-907c-80296f4e2994

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB05_weighted_record_model
title: The weighted record model satisfies the B05 floor whenever every record costs at least the floor
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K1_RecordModel; FOUNDATION_INPUTS B05 (MarginalFloor, as designated).
consumes_inputs: none. This PROVES the B05 predicate in a model; it does not assume it.
statement: (weighted_marginal_ge) in the record model, if every record costs at least eps and d is
 support-novel over S, then adding d raises the family cost by at least eps.
 (APFB05.weighted_record_model_satisfies_floor) so MarginalFloor holds in the model with floor eps, for every
 capacity and with every distinction tested.
consequence: record costs in the model are unequal in general. B05 therefore does not force cost to depend
 only on the number of records. This is an independence statement about that one clause.
not_claimed: that B05 holds because of this; that any interface is a record model.
-/
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFPaper5_K1_familyCost_weighted
import Theorems.Thm_APFPaper5_K1_recordModelCost_eq
import Theorems.Thm_APFPaper5_K1_recordModel_sharedCost
import Theorems.Thm_APFPaper5_K1_recordModel_satisfies_K1

set_option autoImplicit false
open APFPaper1.Source APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec] [DecidableEq ι]

theorem APFPaper5.K1.weighted_marginal_ge (w : Rec → NNReal) (fam : ι → Finset Rec) (eps : ℝ)
    (hw : ∀ a, eps ≤ (w a : ℝ)) (S : Finset ι) (d : ι)
    (hnew : supportNovel (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
      (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
      (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S d) :
    eps ≤ familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) (insert d S) -
      familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
        (fun _ sigma e => (↑(fam e) : Set Rec) ⊆ sigma) (fun _ _ _ => True) S := by
  have hnot : ¬ fam d ⊆ S.biUnion fam := by
    intro hsub
    obtain ⟨eta, heta, hall⟩ := hnew
    refine hall (S.biUnion fam) (fun e he => ⟨↑(S.biUnion fam), subset_rfl,
      Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem fam he), trivial⟩) ?_
      ⟨↑(fam d), Finset.coe_subset.mpr hsub, subset_rfl⟩
    rw [familyCost_weighted w fam S]
    have hc : ((∑ a ∈ S.biUnion fam, w a : NNReal) : ℝ) = ∑ a ∈ S.biUnion fam, (w a : ℝ) :=
      NNReal.coe_sum _ _
    show ((∑ a ∈ S.biUnion fam, w a : NNReal) : ℝ) ≤ _
    rw [hc]
    linarith
  obtain ⟨a, had, haU⟩ := Finset.not_subset.mp hnot
  rw [familyCost_weighted w fam (insert d S), familyCost_weighted w fam S, Finset.biUnion_insert]
  have hsub : insert a (S.biUnion fam) ⊆ fam d ∪ S.biUnion fam := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxU
    · rw [hxa]
      exact Finset.mem_union_left _ had
    · exact Finset.mem_union_right _ hxU
  have hsum : ∑ x ∈ insert a (S.biUnion fam), (w x : ℝ) ≤
      ∑ x ∈ fam d ∪ S.biUnion fam, (w x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => NNReal.coe_nonneg _)
  rw [Finset.sum_insert haU] at hsum
  have hwa := hw a
  linarith

theorem APFB05.weighted_record_model_satisfies_floor {Context : Type*} (w : Rec → NNReal)
    (fam : ι → Finset Rec) (eps : ℝ) (heps : 0 < eps) (hw : ∀ a, eps ≤ (w a : ℝ))
    (C : Context → ℝ) :
    APFB05.MarginalFloor (Context := Context) (D := fun _ => ι) (P := fun _ => Finset Rec)
      (R := fun _ => Finset Rec) (Record := fun _ => Rec)
      (fun _ p => p) (fun _ r => ∑ a ∈ r, w a) (fun _ p => (↑p : Set Rec))
      (fun _ _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ _ => True) (fun _ _ => True)
      C (fun _ => eps) :=
  fun _ => ⟨heps, fun S d _ _ _ hnew => weighted_marginal_ge w fam eps hw S d hnew⟩


universe apfNative_u apfNative_v apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u} {Rec : Type apfNative_v} [DecidableEq.{apfNative_v + 1} Rec]
  [inst : DecidableEq.{apfNative_u + 1} ι] {Context : Type apfNative_u_1} (w : Rec → NNReal)
  (fam : ι → Finset.{apfNative_v} Rec) (eps : Real)
  (heps : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps)
  (hw : ∀ (a : Rec), @LE.le.{0} Real Real.instLE eps (NNReal.toReal (w a))) (C : Context → Real),
  @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u, apfNative_v, apfNative_v, apfNative_v} Context
    (fun (x : Context) => ι) (fun (x : Context) => Finset.{apfNative_v} Rec)
    (fun (x : Context) => Finset.{apfNative_v} Rec) (fun (x : Context) => Rec) (fun (g : Context) => inst)
    (fun (x : Context) (p : Finset.{apfNative_v} Rec) => p)
    (fun (x : Context) (r : Finset.{apfNative_v} Rec) =>
      @Finset.sum.{apfNative_v, 0} Rec NNReal (@Semiring.toAddCommMonoid.{0} NNReal NNReal.instSemiring) r
        fun (a : Rec) => w a)
    (fun (x : Context) (p : Finset.{apfNative_v} Rec) =>
      @SetLike.coe.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec (@Finset.instSetLike.{apfNative_v} Rec) p)
    (fun (x : Context) (x_1 : Finset.{apfNative_v} Rec) (sigma : Set.{apfNative_v} Rec) (d : ι) =>
      @LE.le.{apfNative_v} (Set.{apfNative_v} Rec) (@Set.instLE.{apfNative_v} Rec)
        (@SetLike.coe.{apfNative_v, apfNative_v} (Finset.{apfNative_v} Rec) Rec (@Finset.instSetLike.{apfNative_v} Rec)
          (fam d))
        sigma)
    (fun (x : Context) (x_1 : Finset.{apfNative_v} Rec) (x_2 : ι) (x_3 : Set.{apfNative_v} Rec) => True)
    (fun (x : Context) (x_1 : ι) => True) C fun (x : Context) => eps := by
  exact @APFB05.weighted_record_model_satisfies_floor
