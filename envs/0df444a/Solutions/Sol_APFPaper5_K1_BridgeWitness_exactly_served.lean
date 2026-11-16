-- Prove2me | solution 1 for APFPaper5.K1.BridgeWitness.exactly_served
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:53:52.221209+00:00
-- url     : https://prove2.me/submissions/0ca4378c-cce1-4b4f-b60e-8bdad8f3e346

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_APFPaper5_K1_RecordModel
import Definitions.Def_APFPaper5_K1_SharedCost
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_APFPaper5_K1_interface_bridge_witness_Vocabulary
import Definitions.Def_APFPaper5_K1_interface_bridge_Vocabulary
import Theorems.Thm_APFPaper5_K1_interface_region_satisfies_K1_of_floor
import Theorems.Thm_APFPaper5_K1_weighted_marginal_ge
import Theorems.Thm_APFB05_weighted_record_model_satisfies_floor
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
/-
APF Foundation Ledger — theorem node. DRAFT for author and cold review. Not gated, not released, not uploaded.
name: APFB05.overfull_chain_not_admissible
title: A family built by more genuinely new tested distinctions than the capacity can pay for is not admissible, and a context with less than one floor of spare capacity cannot take one more
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1781 (ledger admissibility), 1820-1824 (marginal floor and support novelty),
  2625 (support novelty, formal). The consumed nodes cite the same passages by their v9.27 line numbers
  (1763-1782, 1807-1818, 2615-2617). For the reading as a statement about classical record models: v9.28:3724,
  3737 (the defender's admissible record space and charging clause), 6952.
consumes: B05 (encoding MarginalFloor, r2, with its tested guard). B04 enters only as the capacity C in
  familyAdmissible. Uses the uploaded node APFB05.support_novel_chain_capacity_bound.
statement:
  (1) familyAdmissible is inherited by subfamilies.
  (2) If S n is built from S 0 by n tested support-novel insertions and C < n * epsilon, then S n is not admissible.
  (3) Then no admissible family contains S n.
  (4) If S is admissible, d is tested and support-novel over S, and C - familyCost S < epsilon, then insert d S is
      not admissible.
no new definition: every statement is in the existing FamilyCost and B05 vocabulary.
what it does not say: nothing about defenders, Sep, IJC or nonclassicality. Reading (3) or (4) as "no classical
  record model exists" needs a definition tying a defender's record family to familyAdmissible. That definition is
  not on the ledger and is not supplied here.
-/






set_option autoImplicit false
open Classical
open APFPaper1.Source

namespace APFB05

/-- (1) Admissibility passes to subfamilies: the same protocol serves the subfamily, and the infimal bill of a
subfamily is at most that of the family. Ordinary mathematics on source data. -/
theorem familyAdmissible_of_subset {D P R Record : Type*}
    (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) {C : ℝ} {S T : Finset D} (hST : S ⊆ T)
    (hT : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C T) :
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S := by
  obtain ⟨⟨p, hp⟩, hcost⟩ := hT
  refine ⟨⟨p, fun d hd => hp d (hST hd)⟩, le_trans ?_ hcost⟩
  unfold familyCost
  apply csInf_le_csInf
  · refine ⟨0, fun c hc => ?_⟩
    obtain ⟨q, _, rfl⟩ := hc
    exact NNReal.coe_nonneg _
  · exact ⟨_, p, hp, rfl⟩
  · rintro c ⟨q, hq, rfl⟩
    exact ⟨q, fun d hd => hq d (hST hd), rfl⟩







end APFB05

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











set_option autoImplicit false
open APFPaper1.Source
namespace APFPaper5.K1

universe u v
variable {ι : Type u} {Rec : Type v} [DecidableEq Rec]





theorem atomTable_eq_sum_inter [Fintype Rec] (w : Rec → ℝ) (fam : ι → Finset Rec) (i j : ι) :
    atomTable w (fun k a => decide (a ∈ fam k)) i j = ∑ a ∈ fam i ∩ fam j, w a := by
  have hterm : ∀ a : Rec, w a * (ind (decide (a ∈ fam i)) * ind (decide (a ∈ fam j))) =
      if a ∈ fam i ∩ fam j then w a else 0 := by
    intro a
    by_cases h1 : a ∈ fam i <;> by_cases h2 : a ∈ fam j <;> simp [ind, Finset.mem_inter, h1, h2]
  unfold atomTable
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]







end APFPaper5.K1


/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_bridge_witness
title: The hypotheses of the K1 interface bridge hold together on a book with one record that all distinctions share and one private record each, and there the shared cost of two different distinctions is 1 and of a distinction with itself is 2
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Thm_APFPaper5_K1_interface_bridge (this seat). Builder seat: APFB05.weighted_record_model_satisfies_floor,
 APFPaper5.K1.recordModel_supportNovel_of_needs_own_record, APFPaper5.K1.familyCost_weighted.
standing: A WORLD. It shows only that the hypotheses of interface_region_satisfies_K1_of_floor can hold
 together, with records that are really shared. It is not a claim about any physical interface.
what this file says: on finitely many distinctions, with records `none` (needed by all) and `some i` (needed
 by i alone), every record costing 1 and the floor 1, the bridge applies; the table it speaks of has 2 on
 the diagonal and 1 off it.
what this file does NOT say: that the declared inputs force this book or any book. No lane. No claim that
 the transfer is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/








set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1.BridgeWitness

variable {ι : Type} [DecidableEq ι]





omit [DecidableEq ι] in
/-- The bill of a kept record set is the sum of its records' costs. -/
theorem bill_is_sum (p : Finset (Option ι)) :
    ((∑ a ∈ p, (w (ι := ι) a) : NNReal) : ℝ) = ∑ r ∈ p, ((w (ι := ι) r : NNReal) : ℝ) :=
  NNReal.coe_sum _ _

theorem exactly_served (S : Finset ι) :
    ExactlyServed (fun p : Finset (Option ι) => (↑p : Set (Option ι)))
      (fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma) (fun _ _ _ => True)
      (fun p : Finset (Option ι) => p) fam S := by
  refine ⟨S.biUnion fam, rfl, fun d hd => ⟨↑(fam d), ?_, subset_rfl, trivial⟩⟩
  exact Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem fam hd)

/-- The bridge applies to this book. -/
theorem bridge_applies [Fintype ι] :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (familyCost (D := ι) (P := Finset (Option ι)) (R := Finset (Option ι))
            (Record := Option ι) (fun p => p) (fun r => ∑ a ∈ r, w a)
            (fun p => (↑p : Set (Option ι)))
            (fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma) (fun _ _ _ => True))
          {i} {j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (familyCost (D := ι) (P := Finset (Option ι)) (R := Finset (Option ι))
            (Record := Option ι) (fun p => p) (fun r => ∑ a ∈ r, w a)
            (fun p => (↑p : Set (Option ι)))
            (fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma) (fun _ _ _ => True))
          {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      familyCost (D := ι) (P := Finset (Option ι)) (R := Finset (Option ι)) (Record := Option ι)
        (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set (Option ι)))
        (fun _ sigma d => (↑(fam d) : Set (Option ι)) ⊆ sigma) (fun _ _ _ => True)
        (Finset.univ.image (fun i : ι => i)) ≤ C := ⟨_, le_refl _⟩
  have hfeas : familyFeasible (fun p : Finset (Option ι) => (↑p : Set (Option ι)))
      (fun (_ : Finset (Option ι)) (sigma : Set (Option ι)) (d : ι) =>
        (↑(fam d) : Set (Option ι)) ⊆ sigma)
      (fun (_ : Finset (Option ι)) (_ : ι) (_ : Set (Option ι)) => True)
      (Finset.univ.image (fun i : ι => i)) := by
    obtain ⟨p, _, hp⟩ := exactly_served (Finset.univ.image (fun i : ι => i))
    exact ⟨p, hp⟩
  have hneeds : ∀ i : ι,
      ¬ fam i ⊆ ((Finset.univ.erase i).image (fun i : ι => i)).biUnion fam := by
    intro i h
    have hi : some i ∈ fam i := by simp [fam]
    have h2 := h hi
    rw [Finset.mem_biUnion] at h2
    obtain ⟨k, hk, hmem⟩ := h2
    rw [Finset.mem_image] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    have hne : k' ≠ i := (Finset.mem_erase.mp hk').1
    simp [fam] at hmem
    exact hne hmem.symm
  exact interface_region_satisfies_K1_of_floor (ι := ι)
    (fun p : Finset (Option ι) => p) (fun r : Finset (Option ι) => ∑ a ∈ r, w a)
    (fun p : Finset (Option ι) => (↑p : Set (Option ι)))
    (fun (_ : Finset (Option ι)) (sigma : Set (Option ι)) (d : ι) =>
      (↑(fam d) : Set (Option ι)) ⊆ sigma)
    (fun (_ : Finset (Option ι)) (_ : ι) (_ : Set (Option ι)) => True)
    (fun p : Finset (Option ι) => p) fam w
    (fun p => bill_is_sum p) (fun _ => rfl) (fun _ _ _ h => h) (fun _ => True) C 1
    (APFB05.weighted_record_model_satisfies_floor (Context := Unit) w fam 1 one_pos
      (fun a => by simp [w]) (fun _ => C))
    (fun S _ => exactly_served S) (fun i : ι => i) (And.intro hfeas hC) (fun _ => trivial)
    (fun i => recordModel_supportNovel_of_needs_own_record w fam 1 one_pos
      (fun a => by simp [w]) _ i (hneeds i))

/-- In this book the shared cost of two different distinctions is the cost of the one shared record. -/
theorem shared_cost_off_diagonal [Fintype ι] (i j : ι) (hij : i ≠ j) :
    sharedCost (recordModelCost w (fam (ι := ι))) {i} {j} = 1 := by
  have hinter : fam i ∩ fam j = ({none} : Finset (Option ι)) := by
    ext a
    cases a with
    | none => simp [fam]
    | some k =>
        simp only [fam, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq, reduceCtorEq, false_or]
        constructor
        · rintro ⟨rfl, h⟩
          exact hij h
        · intro h
          exact absurd h (by simp)
  rw [recordModel_sharedCost, atomTable_eq_sum_inter, hinter]
  simp [w]

/-- In this book the shared cost of a distinction with itself is the cost of its two records. -/
theorem shared_cost_diagonal [Fintype ι] (i : ι) :
    sharedCost (recordModelCost w (fam (ι := ι))) {i} {i} = 2 := by
  rw [recordModel_sharedCost, atomTable_eq_sum_inter, Finset.inter_self]
  simp [fam, w]

end APFPaper5.K1.BridgeWitness


theorem solution :
∀ {ι : Type} [inst : DecidableEq.{1} ι] (S : Finset.{0} ι),
  @APFPaper5.K1.ExactlyServed.{0, 0, 0} ι (Finset.{0} (Option.{0} ι)) (Option.{0} ι)
    (fun (a b : Option.{0} ι) => @Option.instDecidableEq.{0} ι inst a b)
    (fun (p : Finset.{0} (Option.{0} ι)) =>
      @SetLike.coe.{0, 0} (Finset.{0} (Option.{0} ι)) (Option.{0} ι) (@Finset.instSetLike.{0} (Option.{0} ι)) p)
    (fun (x : Finset.{0} (Option.{0} ι)) (sigma : Set.{0} (Option.{0} ι)) (d : ι) =>
      @LE.le.{0} (Set.{0} (Option.{0} ι)) (@Set.instLE.{0} (Option.{0} ι))
        (@SetLike.coe.{0, 0} (Finset.{0} (Option.{0} ι)) (Option.{0} ι) (@Finset.instSetLike.{0} (Option.{0} ι))
          (@APFPaper5.K1.BridgeWitness.fam ι inst d))
        sigma)
    (fun (x : Finset.{0} (Option.{0} ι)) (x_1 : ι) (x_2 : Set.{0} (Option.{0} ι)) => True)
    (fun (p : Finset.{0} (Option.{0} ι)) => p) (@APFPaper5.K1.BridgeWitness.fam ι inst) S := by
  exact @APFPaper5.K1.BridgeWitness.exactly_served
