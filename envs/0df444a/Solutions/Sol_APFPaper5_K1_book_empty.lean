-- Prove2me | solution 1 for APFPaper5.K1.book_empty
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:33:23.932197+00:00
-- url     : https://prove2.me/submissions/cee244c9-6602-4d74-865a-40e78f4f3057

import Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_cost_book
title: Every cost on the families of a finite set of distinctions is the cost of a book of records, one record for each set of distinctions and needed by exactly those; the shared cost of two distinctions is the cost of the records both need; and where no record has negative cost and each distinction's own record has positive cost, the table meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:26: "The record ledger can be derived - each item in it". 20:31:
 "Yes" (to typing the derivation: the book of a cost function, the identity, and K1 from B05 plus
 nonnegative shared costs). NOTE_record_ledger_can_be_derived_2026-11-14. Builder seat:
 Def_APFPaper5_K1_MarkTable (atomTable), Def_APFPaper5_K1_SharedCost, record_book_table_satisfies_K1.
 The mathematics is inversion over subsets (Moebius inversion on a finite Boolean lattice), stated here
 through its defining recursion.
standing: THEOREMS ABOUT ANY REAL-VALUED FUNCTION OF FINITE FAMILIES. No input is consumed and no reading is
 used. Nothing is assumed of the cost except, in the last theorem, the three stated sign conditions.
what this file says:
 1. bookCost, book: the cost of the record needed by exactly the members of T, defined by the recursion
    "what T adds over the rest, less the costs of the records of the proper subsets of T".
 2. cost_eq_sum_book: the cost of a family is the cost of the empty family plus the costs of the records
    that some member of the family needs. An identity, for every cost function.
 3. book_empty, book_singleton: the record of no distinction costs nothing; the record a distinction needs
    alone costs what that distinction adds over all the others.
 4. sharedCost_eq_atomTable_book: the shared cost of two distinctions is the total cost of the records
    both need, the cost of the empty family being carried on the record that all need.
 5. cost_table_satisfies_K1: if the empty family costs at least nothing, no record has negative cost, and
    each distinction's own record has positive cost, the table of shared costs is bilinear with a
    nonnegative and faithful diagonal under the identity role exchange.
what this file does NOT say:
 - That the record costs are nonnegative. They can be negative; that is a property of the cost function.
 - That the book is the only one (it is, by the same inversion; not typed), or the closed alternating-sum
   formula for a record's cost (not typed), or that nonnegative record costs is the same as the cost being
   completely alternating (classical; not typed).
 - Anything about a single protocol's bill.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper5.K1

variable {ι : Type} [DecidableEq ι]



theorem bookCost_eq (g : Finset ι → ℝ) (A : Finset ι) :
    bookCost g A = g A - ∑ T ∈ A.ssubsets, bookCost g T := by
  have h : bookCost g A = g A - ∑ T ∈ A.ssubsets.attach, bookCost g T.1 :=
    Finset.strongInduction_eq (p := fun _ => ℝ) _ A
  rw [h, Finset.sum_attach A.ssubsets (fun T => bookCost g T)]

/-- The records of the subsets of `A` cost `g A` in all. -/
theorem sum_powerset_bookCost (g : Finset ι → ℝ) (A : Finset ι) :
    ∑ T ∈ A.powerset, bookCost g T = g A := by
  have hmem : A ∈ A.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl A)
  rw [← Finset.add_sum_erase A.powerset (bookCost g) hmem]
  have hss : A.powerset.erase A = A.ssubsets := rfl
  rw [hss, bookCost_eq g A]
  ring

variable [Fintype ι]





/-- The cost of a family is the cost of the empty family plus the costs of the records that some member
of the family needs. -/
theorem cost_eq_sum_book (f : Finset ι → ℝ) (S : Finset ι) :
    f S = f ∅ + ∑ T : Finset ι, (if Disjoint T S then 0 else book f T) := by
  have h1 : ∑ T : Finset ι, book f T = f Finset.univ - f ∅ := by
    have h := sum_powerset_bookCost (addsOverRest f) Finset.univ
    rw [Finset.powerset_univ] at h
    simpa [book, addsOverRest] using h
  have h2 : ∑ T ∈ Sᶜ.powerset, book f T = f Finset.univ - f S := by
    have h := sum_powerset_bookCost (addsOverRest f) Sᶜ
    simpa [book, addsOverRest] using h
  have hfilt : (Finset.univ : Finset (Finset ι)).filter (fun T => Disjoint T S) = Sᶜ.powerset := by
    ext T
    simp [Finset.subset_compl_iff_disjoint_right]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset ι))
    (fun T => Disjoint T S) (book f)
  have hite : ∑ T : Finset ι, (if Disjoint T S then 0 else book f T) =
      ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T => ¬ Disjoint T S), book f T := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    by_cases h : Disjoint T S <;> simp [h]
  rw [hite]
  rw [hfilt] at hsplit
  linarith

/-- The record of no distinction costs nothing. -/
theorem book_empty (f : Finset ι → ℝ) : book f ∅ = 0 := by
  have h := sum_powerset_bookCost (addsOverRest f) ∅
  rw [Finset.powerset_empty, Finset.sum_singleton] at h
  simpa [book, addsOverRest] using h

/-- The record a distinction needs alone costs what that distinction adds over all the others. -/
theorem book_singleton (f : Finset ι → ℝ) (i : ι) : book f {i} = f Finset.univ - f {i}ᶜ := by
  have hss : ({i} : Finset ι).ssubsets = {∅} := by
    ext T
    simp [Finset.mem_ssubsets, Finset.ssubset_singleton_iff]
  have h := bookCost_eq (addsOverRest f) {i}
  rw [hss, Finset.sum_singleton] at h
  have h0 := book_empty f
  have hg : addsOverRest f {i} = f Finset.univ - f {i}ᶜ := rfl
  unfold book at h0 ⊢
  rw [h, h0, hg]
  ring



/-- The shared cost of two distinctions is the total cost of the records both need. -/
theorem sharedCost_eq_atomTable_book (f : Finset ι → ℝ) (i j : ι) :
    sharedCost f {i} {j} = atomTable (bookWeight f) (fun k T => decide (k ∈ T)) i j := by
  have hi := cost_eq_sum_book f {i}
  have hj := cost_eq_sum_book f {j}
  have hij := cost_eq_sum_book f ({i} ∪ {j})
  have key : ∀ T : Finset ι,
      book f T * (ind (decide (i ∈ T)) * ind (decide (j ∈ T))) =
        (if Disjoint T {i} then 0 else book f T) + (if Disjoint T {j} then 0 else book f T) -
          (if Disjoint T ({i} ∪ {j}) then 0 else book f T) := by
    intro T
    by_cases h1 : i ∈ T <;> by_cases h2 : j ∈ T <;>
      simp [h1, h2, ind]
  have hsum : ∑ T : Finset ι, book f T * (ind (decide (i ∈ T)) * ind (decide (j ∈ T))) =
      f {i} + f {j} - f ({i} ∪ {j}) - f ∅ := by
    rw [Finset.sum_congr rfl (fun T _ => key T), Finset.sum_sub_distrib, Finset.sum_add_distrib]
    linarith
  have hc : ∑ T : Finset ι, (if T = Finset.univ then f ∅ else 0) *
      (ind (decide (i ∈ T)) * ind (decide (j ∈ T))) = f ∅ := by
    rw [Finset.sum_eq_single (Finset.univ : Finset ι)]
    · simp [ind]
    · intro T _ hT
      simp [hT]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold sharedCost atomTable bookWeight
  simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum, hc]
  ring

/-- K1's typed conditions for the table of shared costs, from three sign conditions on the cost. -/
theorem cost_table_satisfies_K1 (f : Finset ι → ℝ) (h0 : 0 ≤ f ∅)
    (hnonneg : ∀ T : Finset ι, 0 ≤ book f T) (hprivate : ∀ i : ι, 0 < book f {i}) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (fun i j : ι => sharedCost f {i} {j})) ∧
      FaithfulNonnegDiagonal (tableForm (fun i j : ι => sharedCost f {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have htab : (fun i j : ι => sharedCost f {i} {j}) =
      atomTable (bookWeight f) (fun k T => decide (k ∈ T)) := by
    funext i j
    exact sharedCost_eq_atomTable_book f i j
  rw [htab]
  refine record_book_table_satisfies_K1 (bookWeight f) ?_ _ ?_
  · intro T
    unfold bookWeight
    have := hnonneg T
    split_ifs <;> linarith
  · intro i
    refine ⟨{i}, ?_, fun j => by simp⟩
    unfold bookWeight
    have := hprivate i
    split_ifs <;> linarith

end APFPaper5.K1


theorem solution :
∀ {ι : Type} [inst : DecidableEq.{1} ι] [inst_1 : Fintype.{0} ι] (f : Finset.{0} ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.book ι inst inst_1 f
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} ι) (@Finset.instEmptyCollection.{0} ι)))
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper5.K1.book_empty
