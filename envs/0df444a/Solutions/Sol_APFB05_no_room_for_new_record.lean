-- Prove2me | solution 1 for APFB05.no_room_for_new_record
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:59:17.010289+00:00
-- url     : https://prove2.me/submissions/0bc8fbad-3ae3-4ac8-8631-f123fd6dcf5f

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
import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Theorems.Thm_APFB05_support_novel_chain_capacity_bound
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

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

/-- (2) An overfull chain is not admissible. Contrapositive of the rank bound. -/
theorem overfull_chain_not_admissible
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hover : C g < (n : ℝ) * epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S n) := by
  intro hadm
  have h := (APFB05.support_novel_chain_capacity_bound wholeResource calibration maintained sufficient
    usesToRealize tested C epsilon hB05 g n S d hstep htested hnovel hadm).1
  linarith [hadm.2]

/-- (3) No admissible family contains an overfull chain. -/
theorem no_admissible_family_contains_overfull_chain
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hover : C g < (n : ℝ) * epsilon g)
    (T : Finset (D g)) (hT : S n ⊆ T) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) T :=
  fun hadm => overfull_chain_not_admissible wholeResource calibration maintained sufficient usesToRealize
    tested C epsilon hB05 g n S d hstep htested hnovel hover
    (familyAdmissible_of_subset (wholeResource g) (calibration g) (maintained g) (sufficient g)
      (usesToRealize g) hT hadm)

/-- (4) No room for one more. If the spare capacity over an admissible family `S` is less than the floor, a
tested distinction that is support-novel over `S` cannot be added admissibly. Directly from B05. -/
theorem no_room_for_new_record
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (S : Finset (D g)) (d : D g)
    (htested : tested g d)
    (hS : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) S)
    (hnovel : supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S d)
    (hspare : C g - familyCost (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) S < epsilon g) :
    ¬ familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (insert d S) := by
  intro hins
  have h := (hB05 g).2 S d htested hS hins hnovel
  linarith [hins.2]

end APFB05


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
  (g : Context) (S : Finset.{apfNative_u_2} (D g)) (d : D g) (htested : tested g d)
  (hS :
    @APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g) S)
  (hnovel :
    @APFPaper1.Source.supportNovel.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S d)
  (hspare :
    @LT.lt.{0} Real Real.instLT
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (C g)
        (@APFPaper1.Source.familyCost.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
          (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) S))
      (epsilon g)),
  Not
    (@APFPaper1.Source.familyAdmissible.{apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} (D g) (P g) (R g)
      (Record g) (wholeResource g) (calibration g) (maintained g) (sufficient g) (usesToRealize g) (C g)
      (@Insert.insert.{apfNative_u_2, apfNative_u_2} (D g) (Finset.{apfNative_u_2} (D g))
        (@Finset.instInsert.{apfNative_u_2} (D g) (inst g)) d S)) := by
  exact @APFB05.no_room_for_new_record
