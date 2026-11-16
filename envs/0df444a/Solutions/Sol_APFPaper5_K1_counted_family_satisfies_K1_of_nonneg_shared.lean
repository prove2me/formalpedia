-- Prove2me | solution 1 for APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:32:00.786881+00:00
-- url     : https://prove2.me/submissions/dc5701dc-0ab9-4cfb-8781-28999e6a53df

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_APFPaper5_K1_interface_cost_book_Vocabulary
import Definitions.Def_APFPaper5_K1_cost_book_Vocabulary
import Theorems.Thm_APFPaper5_K1_book_empty
import Theorems.Thm_APFPaper5_K1_book_singleton
import Theorems.Thm_APFPaper5_K1_cost_table_satisfies_K1
import Theorems.Thm_APFB05_overfull_chain_not_admissible
import Theorems.Thm_APFB05_no_admissible_family_contains_overfull_chain
import Theorems.Thm_APFB05_no_room_for_new_record
import Theorems.Thm_APFPaper1_Source_familyCost_nonneg
import Theorems.Thm_APFPaper1_Source_familyCost_mono
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
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_interface_cost_book
title: On any source data of the declared forms, for a counted family, the declared B05 makes each distinction's own record cost at least the floor; if in addition no record needed by two or more of them has negative cost, the table of shared costs meets K1's typed conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 HST. 20:26: "The record ledger can be derived - each item in it". 20:31:
 "Yes". Thm_APFPaper5_K1_cost_book (this seat). Declared input B05 in its declared form
 APFB05.MarginalFloor (Def_APF_B05_DeclaredInput_r2). Builder seat: APFB05.familyAdmissible_of_subset,
 APFPaper1.Source.familyCost_nonneg.
standing: THEOREMS ON THE DECLARED FORMS. No record ledger is assumed, no reading about bills is used, and
 the availability sentence is not used. The premises are:
 - hB05: the DECLARED INPUT B05.
 - hregion, htested, hnov: the family is a counted family in the sense the author ruled as call 2 at 19:57
   HST (finite, within capacity, each member tested and support-novel over the others).
 - hshared: no record needed by two or more of the counted distinctions has negative cost. This is the ONE
   premise that is neither an input nor a definition. It is a property of the family's costs: sharing
   never costs extra, at each order. It is NOT DERIVED here and NOT ADOPTED. Whether it follows from
   anything the author holds, or fails in a world meeting the eight, is not settled.
what this file says:
 1. counted_own_record_ge_floor: under B05, in a counted family, the record a distinction needs alone
    costs at least the floor.
 2. counted_family_satisfies_K1_of_nonneg_shared: with hshared as well, the table of shared costs of the
    counted family is bilinear with a nonnegative and faithful diagonal.
what this file does NOT say: that hshared holds. That the role exchange is anything but the identity.
 Anything about orientation, K2 to K6 or the K3 models. No lane. No claim that the transfer is forced, that
 the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/











set_option autoImplicit false

open APFPaper1.Source

namespace APFPaper5.K1

section
variable {D P R Record : Type*} [DecidableEq D] {ι : Type} [Fintype ι] [DecidableEq ι]
  (wholeResource : P → R) (calibration : R → NNReal)
  (maintained : P → Set Record)
  (sufficient : P → Set Record → D → Prop)
  (usesToRealize : P → D → Set Record → Prop)



/-- Under B05, in a counted family, the record a distinction needs alone costs at least the floor. -/
theorem counted_own_record_ge_floor (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (dist : ι → D)
    (hregion : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (Finset.univ.image dist))
    (htested : ∀ i, tested (dist i))
    (hnov : ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
      ((({i} : Finset ι)ᶜ).image dist) (dist i))
    (i : ι) :
    0 < eps ∧ eps ≤ book (indexedCost wholeResource calibration maintained sufficient usesToRealize
      dist) {i} := by
  obtain ⟨heps, hfl⟩ := hB05 ()
  have hins : insert (dist i) ((({i} : Finset ι)ᶜ).image dist) = Finset.univ.image dist := by
    rw [← Finset.image_insert]
    congr 1
    ext x
    simp
  have hsub : (({i} : Finset ι)ᶜ).image dist ⊆ Finset.univ.image dist :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hadm := APFB05.familyAdmissible_of_subset wholeResource calibration maintained sufficient
    usesToRealize hsub hregion
  have hadm' : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (insert (dist i) ((({i} : Finset ι)ᶜ).image dist)) := by
    rw [hins]
    exact hregion
  have hgap := hfl ((({i} : Finset ι)ᶜ).image dist) (dist i) (htested i) hadm hadm' (hnov i)
  rw [hins] at hgap
  refine ⟨heps, ?_⟩
  rw [book_singleton]
  exact hgap

/-- K1's typed conditions for the shared costs of a counted family, from the declared B05 and the one
premise that no record needed by two or more has negative cost. -/
theorem counted_family_satisfies_K1_of_nonneg_shared (tested : D → Prop) (C eps : ℝ)
    (hB05 : APFB05.MarginalFloor (Context := Unit) (D := fun _ => D) (P := fun _ => P)
      (R := fun _ => R) (Record := fun _ => Record) (fun _ => wholeResource) (fun _ => calibration)
      (fun _ => maintained) (fun _ => sufficient) (fun _ => usesToRealize) (fun _ => tested)
      (fun _ => C) (fun _ => eps))
    (dist : ι → D)
    (hregion : familyAdmissible wholeResource calibration maintained sufficient usesToRealize C
      (Finset.univ.image dist))
    (htested : ∀ i, tested (dist i))
    (hnov : ∀ i, supportNovel wholeResource calibration maintained sufficient usesToRealize
      ((({i} : Finset ι)ᶜ).image dist) (dist i))
    (hshared : ∀ T : Finset ι, 2 ≤ T.card →
      0 ≤ book (indexedCost wholeResource calibration maintained sufficient usesToRealize dist) T) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ)
        (tableForm (fun i j : ι => sharedCost
          (indexedCost wholeResource calibration maintained sufficient usesToRealize dist)
          {i} {j})) ∧
      FaithfulNonnegDiagonal
        (tableForm (fun i j : ι => sharedCost
          (indexedCost wholeResource calibration maintained sufficient usesToRealize dist)
          {i} {j}))
        (LinearEquiv.refl ℝ (ι → ℝ)) := by
  have hpriv : ∀ i : ι,
      0 < book (indexedCost wholeResource calibration maintained sufficient usesToRealize dist) {i} := by
    intro i
    obtain ⟨heps, hle⟩ := counted_own_record_ge_floor wholeResource calibration maintained sufficient
      usesToRealize tested C eps hB05 dist hregion htested hnov i
    linarith
  have h0 : 0 ≤ indexedCost wholeResource calibration maintained sufficient usesToRealize dist ∅ :=
    familyCost_nonneg wholeResource calibration maintained sufficient usesToRealize _
  have hnonneg : ∀ T : Finset ι,
      0 ≤ book (indexedCost wholeResource calibration maintained sufficient usesToRealize dist) T := by
    intro T
    by_cases h2 : 2 ≤ T.card
    · exact hshared T h2
    · rcases Nat.eq_zero_or_pos T.card with hz | hp
      · rw [Finset.card_eq_zero.mp hz, book_empty]
      · have h1 : T.card = 1 := by omega
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        exact (hpriv a).le
  exact cost_table_satisfies_K1 _ h0 hnonneg hpriv

end

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  [inst : DecidableEq.{apfNative_u_1 + 1} D] {ι : Type} [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι]
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (tested : D → Prop) (C eps : Real)
  (hB05 :
    @APFB05.MarginalFloor.{0, apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} Unit (fun (x : Unit) => D)
      (fun (x : Unit) => P) (fun (x : Unit) => R) (fun (x : Unit) => Record) (fun (g : Unit) => inst)
      (fun (x : Unit) => wholeResource) (fun (x : Unit) => calibration) (fun (x : Unit) => maintained)
      (fun (x : Unit) => sufficient) (fun (x : Unit) => usesToRealize) (fun (x : Unit) => tested) (fun (x : Unit) => C)
      fun (x : Unit) => eps)
  (dist : ι → D)
  (hregion :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize C
      (@Finset.image.{0, apfNative_u_1} ι D inst dist (@Finset.univ.{0} ι inst_1)))
  (htested : ∀ (i : ι), tested (dist i))
  (hnov :
    ∀ (i : ι),
      @APFPaper1.Source.supportNovel.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize
        (@Finset.image.{0, apfNative_u_1} ι D inst dist
          (@Compl.compl.{0} (Finset.{0} ι)
            (@BooleanAlgebra.toCompl.{0} (Finset.{0} ι) (@Finset.booleanAlgebra.{0} ι inst_1 inst_2))
            (@Singleton.singleton.{0, 0} ι (Finset.{0} ι) (@Finset.instSingleton.{0} ι) i)))
        (dist i))
  (hshared :
    ∀ (T : Finset.{0} ι),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Finset.card.{0} ι T) →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@APFPaper5.K1.book ι inst_2 inst_1
            (@APFPaper5.K1.indexedCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record inst ι
              wholeResource calibration maintained sufficient usesToRealize dist)
            T)),
  And
    (@APFPaper5.K1.IsBilinear.{0, 0} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{0, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} ι Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{0} ι inst_1 fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{0} ι inst_2
          (@APFPaper5.K1.indexedCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record inst ι
            wholeResource calibration maintained sufficient usesToRealize dist)
          (@Singleton.singleton.{0, 0} ι (Finset.{0} ι) (@Finset.instSingleton.{0} ι) i)
          (@Singleton.singleton.{0, 0} ι (Finset.{0} ι) (@Finset.instSingleton.{0} ι) j)))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0} (ι → Real) (ι → Real)
      (@Pi.addCommGroup.{0, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@APFPaper5.K1.tableForm.{0} ι inst_1 fun (i j : ι) =>
        @APFPaper5.K1.sharedCost.{0} ι inst_2
          (@APFPaper5.K1.indexedCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record inst ι
            wholeResource calibration maintained sufficient usesToRealize dist)
          (@Singleton.singleton.{0, 0} ι (Finset.{0} ι) (@Finset.instSingleton.{0} ι) i)
          (@Singleton.singleton.{0, 0} ι (Finset.{0} ι) (@Finset.instSingleton.{0} ι) j))
      (@LinearEquiv.refl.{0, 0} Real (ι → Real) Real.semiring
        (@Pi.addCommMonoid.{0, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAddCommMonoid)
        (@Pi.Function.module.{0, 0, 0} ι Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.counted_family_satisfies_K1_of_nonneg_shared
