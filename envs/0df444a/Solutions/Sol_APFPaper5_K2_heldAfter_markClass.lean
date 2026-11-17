-- Prove2me | solution 1 for APFPaper5.K2.heldAfter_markClass
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:50:19.627197+00:00
-- url     : https://prove2.me/submissions/aa9211eb-70d5-426f-88e3-f9af3276a37c

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_hold_score
title: With a hold in the channel K2's score is K1's table read on rearranged distinctions; the reverse of a hold is its inverse exactly when the hold keeps the table
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 11:56 HST, "C, proceed as suggested"
 (RULING_K2_score_is_K1s_score_through_the_word_2026-11-15). Def_APFPaper5_K2_HoldScore.
source: Paper 5 Supplement v7.33:396-420 (the score with a process in the channel; orientation closure),
 723-737 (the metric adjoint), 846-864 (physical reversal is a separate claim), 3042-3048 (K2). The builder
 seat's Def_APFB02_HoldOnDistinctions, Thm_APFPaper5_K1_mark_table, Thm_APFPaper5_K1_mark_table_instance;
 this seat's Thm_APFPaper5_K1_identity_exchange (markClass, the ruled score is symmetric).
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
theorems:
 - (rearrangesFamily_id, rearrangesFamily_comp) doing nothing rearranges by the identity; two holds one
   after the other rearrange by the two rearrangements composed.
 - (nothingDrawn_of_rearranges, exists_rearranges_of_nothingDrawn) on all the distinctions of a region, a
   rearrangement with sides exists exactly when nothing is drawn (the adopted reading).
 - (heldAfter_id, heldAfter_comp, heldAfter_add, heldAfter_smul, heldAfter_markClass) what a hold makes of
   what is held is linear, composes, and takes the class of a distinction to the class of the distinction it
   has become.
 - (holdScore_id) the score through a hold that rearranges nothing is K1's form. This covers every hold that
   only changes sides: the side a distinction is read on does not enter the score.
 - (holdScore_marks) on two distinctions, the score through a hold is K1's table between the distinction the
   held one has become and the one read.
 - (holdScore_isBilinear) the score through a hold is bilinear.
 - (holdScore_eq_sum, holdScoreNull_iff_tables) a combination of holds is one no score can see exactly when
   the same combination of their rearranged tables is zero entry by entry. So what the scores see of the
   holds lies among the tables on the listed distinctions: finitely many numbers when the list is finite.
 - (reverse_is_inverse_of_keeps, keeps_of_reverse_is_inverse, reverse_is_inverse_iff_keeps) the score
   through a hold equals K1's form with the inverse rearrangement put on the test side, for all classes,
   exactly when the hold keeps the table.
 - (tableForm_heldAfter_of_keeps) then the hold keeps K1's form.
 - (ends_reversed_of_keeps) then, for a symmetric table, reversing the two ends and putting the inverse hold
   in the channel gives the same score: Paper 5's orientation closure, for holds.
 - (keepsTable_diag, not_keepsTable_of_diag_ne) a hold that keeps the table carries each distinction to one
   of the same diagonal entry; one that does not, does not keep the table.
 - (source_hold_score_marks, source_hold_ends_reversed) the same for the ruled score on source data of the
   declared forms.
named hypothesis: KeepsTable, wherever it appears. It is NOT derived and NOT an adopted reading. The records
 live on the source data and a hold is a map of states; nothing typed ties them.
not claimed:
 - That any hold keeps the table. That the reverse of a hold is admitted.
 - Any score through a word that is not a hold.
 - That a side enters any score. Under K1 as ruled it does not, so a turn-over alone is not seen here.
 - A number for a completed word at a raw input: no rule takes a raw possibility to a class.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
   derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_HoldScore
import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
import Theorems.Thm_APFPaper5_K1_tableForm_markClass
import Theorems.Thm_APFPaper5_K1_table_linearizes
import Theorems.Thm_APFPaper5_K1_nondegenerate_of_faithful_identity
import Theorems.Thm_APFPaper5_K1_orientationForm_zero_of_symm
import Theorems.Thm_APFPaper5_K1_ledgerForm_eq_of_symm
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_symm
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_all_of_K1_with_identity_exchange
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD uK
variable {ι : Type uI}

/-! ### Holds and the adopted reading -/

theorem rearrangesFamily_id_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D) :
    RearrangesFamily reads dist id id (fun _ => false) :=
  fun i x => (Bool.false_xor (reads (dist i) x)).symm

/-- Two holds, one after the other, rearrange by the two rearrangements composed. -/
theorem rearrangesFamily_comp_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (dist : ι → D)
    (h₁ h₂ : X → X) (s₁ s₂ : ι → ι) (f₁ f₂ : ι → Bool)
    (r₁ : RearrangesFamily reads dist h₁ s₁ f₁) (r₂ : RearrangesFamily reads dist h₂ s₂ f₂) :
    RearrangesFamily reads dist (h₂ ∘ h₁) (s₁ ∘ s₂) (fun i => xor (f₂ i) (f₁ (s₂ i))) := by
  intro i x
  show reads (dist i) (h₂ (h₁ x)) = xor (xor (f₂ i) (f₁ (s₂ i))) (reads (dist (s₁ (s₂ i))) x)
  rw [r₂ i (h₁ x), r₁ (s₂ i) x, Bool.xor_assoc]

/-- A rearrangement with sides, on all the distinctions of a region, draws nothing. -/
theorem nothingDrawn_of_rearranges_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool) (h : X → X)
    (sigma : D → D) (flip : D → Bool) (r : RearrangesFamily reads id h sigma flip) :
    APFB02.NothingDrawn reads h :=
  fun d => ⟨sigma d, flip d, fun x => r d x⟩

/-- Where nothing is drawn there is a rearrangement with sides. -/
theorem exists_rearranges_of_nothingDrawn_p2mProof {X : Type uX} {D : Type uD} (reads : D → X → Bool)
    (h : X → X) (hn : APFB02.NothingDrawn reads h) :
    ∃ (sigma : D → D) (flip : D → Bool), RearrangesFamily reads id h sigma flip :=
  ⟨fun d => (hn d).choose, fun d => (hn d).choose_spec.choose,
    fun d x => (hn d).choose_spec.choose_spec x⟩

/-! ### What a hold makes of what is held -/

theorem heldAfter_id_p2mProof (x : ι → ℝ) : heldAfter id x = x := rfl

theorem heldAfter_comp_p2mProof (s₁ s₂ : ι → ι) (x : ι → ℝ) :
    heldAfter (s₁ ∘ s₂) x = heldAfter s₂ (heldAfter s₁ x) := rfl

theorem heldAfter_add_p2mProof (sigma : ι → ι) (x x' : ι → ℝ) :
    heldAfter sigma (x + x') = heldAfter sigma x + heldAfter sigma x' := rfl

theorem heldAfter_smul_p2mProof (sigma : ι → ι) (r : ℝ) (x : ι → ℝ) :
    heldAfter sigma (r • x) = r • heldAfter sigma x := rfl

section
variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The class of a distinction held becomes the class of the distinction it has become. -/
theorem heldAfter_markClass_p2mProof (sigma : Equiv.Perm ι) (e : ι) :
    heldAfter sigma (markClass e) = markClass (sigma.symm e) := by
  funext d
  show (if sigma d = e then (1 : ℝ) else 0) = if d = sigma.symm e then 1 else 0
  by_cases h : sigma d = e
  · rw [if_pos h, if_pos (by rw [← h, Equiv.symm_apply_apply])]
  · rw [if_neg h, if_neg (fun hd => h (by rw [hd, Equiv.apply_symm_apply]))]

/-! ### The score through a hold -/

omit [DecidableEq ι] in
/-- Through a hold that rearranges nothing the score is K1's form. Sides do not enter. -/
theorem holdScore_id_p2mProof (G : ι → ι → ℝ) (x y : ι → ℝ) : holdScore G id x y = tableForm G x y := rfl

/-- On two distinctions: K1's table between the distinction the held one has become and the one read. -/
theorem holdScore_marks_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (e d : ι) :
    holdScore G sigma (markClass e) (markClass d) = G (sigma.symm e) d := by
  unfold holdScore
  rw [heldAfter_markClass_p2mProof, tableForm_markClass]

omit [DecidableEq ι] in
theorem holdScore_isBilinear_p2mProof (G : ι → ι → ℝ) (sigma : ι → ι) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (holdScore G sigma) := by
  obtain ⟨h1, h2, h3, h4⟩ := tableForm_isBilinear G
  exact ⟨fun e e' p => h1 (heldAfter sigma e) (heldAfter sigma e') p,
    fun r e p => h2 r (heldAfter sigma e) p,
    fun e p p' => h3 (heldAfter sigma e) p p', fun r e p => h4 r (heldAfter sigma e) p⟩

omit [DecidableEq ι] in
/-- The score through a hold is the form of the table with its held side rearranged. -/
theorem holdScore_eq_sum_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (x y : ι → ℝ) :
    holdScore G sigma x y = ∑ a, ∑ j, x a * G (sigma.symm a) j * y j := by
  have e := Equiv.sum_comp sigma (fun a => ∑ j, x a * G (sigma.symm a) j * y j)
  rw [← e]
  unfold holdScore tableForm heldAfter
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Equiv.symm_apply_apply]

omit [DecidableEq ι] in
theorem tableForm_heldAfter_right (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (x y : ι → ℝ) :
    tableForm G x (heldAfter sigma.symm y) = ∑ a, ∑ j, x a * G a (sigma j) * y j := by
  unfold tableForm heldAfter
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have e := Equiv.sum_comp sigma (fun b => x a * G a b * y (sigma.symm b))
  rw [← e]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Equiv.symm_apply_apply]

/-! ### The reverse of a hold is its inverse exactly when the hold keeps the table -/

omit [DecidableEq ι] in
theorem reverse_is_inverse_of_keeps_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι)
    (hk : KeepsTable G sigma) (x y : ι → ℝ) :
    holdScore G sigma x y = tableForm G x (heldAfter sigma.symm y) := by
  rw [holdScore_eq_sum_p2mProof, tableForm_heldAfter_right]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => ?_))
  have h := hk (sigma.symm a) j
  rw [Equiv.apply_symm_apply] at h
  rw [h]

theorem keeps_of_reverse_is_inverse_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι)
    (h : ∀ x y : ι → ℝ, holdScore G sigma x y = tableForm G x (heldAfter sigma.symm y)) :
    KeepsTable G sigma := by
  intro a b
  have e := h (markClass (sigma a)) (markClass b)
  rw [holdScore_marks_p2mProof, Equiv.symm_apply_apply] at e
  have e2 : heldAfter (sigma.symm : ι → ι) (markClass b) = markClass (sigma b) := by
    have e3 := heldAfter_markClass_p2mProof sigma.symm b
    rw [Equiv.symm_symm] at e3
    exact e3
  rw [e2, tableForm_markClass] at e
  exact e.symm

theorem reverse_is_inverse_iff_keeps_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) :
    (∀ x y : ι → ℝ, holdScore G sigma x y = tableForm G x (heldAfter sigma.symm y)) ↔
      KeepsTable G sigma :=
  ⟨keeps_of_reverse_is_inverse_p2mProof G sigma, fun hk x y => reverse_is_inverse_of_keeps_p2mProof G sigma hk x y⟩

omit [DecidableEq ι] in
/-- A hold that keeps the table keeps K1's form. -/
theorem tableForm_heldAfter_of_keeps_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι)
    (hk : KeepsTable G sigma) (x y : ι → ℝ) :
    tableForm G (heldAfter sigma x) (heldAfter sigma y) = tableForm G x y := by
  have h := reverse_is_inverse_of_keeps_p2mProof G sigma hk x (heldAfter sigma y)
  have e : heldAfter (sigma.symm : ι → ι) (heldAfter sigma y) = y := by
    funext d
    show y (sigma (sigma.symm d)) = y d
    rw [Equiv.apply_symm_apply]
  rw [e] at h
  exact h

omit [DecidableEq ι] in
/-- For a symmetric table and a hold that keeps it: reversing the two ends, with the inverse hold in the
channel, gives the same score. -/
theorem ends_reversed_of_keeps_p2mProof (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i) (sigma : Equiv.Perm ι)
    (hk : KeepsTable G sigma) (x y : ι → ℝ) :
    holdScore G sigma x y = holdScore G sigma.symm y x := by
  rw [reverse_is_inverse_of_keeps_p2mProof G sigma hk x y]
  exact tableForm_symm G hG x (heldAfter sigma.symm y)

omit [Fintype ι] [DecidableEq ι] in
theorem keepsTable_diag_p2mProof (G : ι → ι → ℝ) (sigma : ι → ι) (hk : KeepsTable G sigma) (a : ι) :
    G (sigma a) (sigma a) = G a a := hk a a

omit [Fintype ι] [DecidableEq ι] in
theorem not_keepsTable_of_diag_ne_p2mProof (G : ι → ι → ℝ) (sigma : ι → ι) (a : ι)
    (h : G (sigma a) (sigma a) ≠ G a a) : ¬ KeepsTable G sigma := fun hk => h (hk a a)

/-! ### What the scores see of the holds -/

/-- A combination of holds is one no score can see exactly when the same combination of their rearranged
tables is zero, entry by entry. -/
theorem holdScoreNull_iff_tables_p2mProof {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
    (sigma : κ → Equiv.Perm ι) :
    HoldScoreNull G coef (fun k => (sigma k : ι → ι)) ↔
      ∀ a j : ι, ∑ k, coef k * G ((sigma k).symm a) j = 0 := by
  constructor
  · intro h a j
    have e := h (markClass a) (markClass j)
    simpa only [holdScore_marks_p2mProof] using e
  · intro h x y
    show ∑ k, coef k * holdScore G (sigma k) x y = 0
    simp only [holdScore_eq_sum_p2mProof, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have e := h a j
    have e' : ∑ k, coef k * (x a * G ((sigma k).symm a) j * y j) =
        x a * y j * ∑ k, coef k * G ((sigma k).symm a) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [e', e, mul_zero]

end

/-! ### On source data of the declared forms, for the ruled score -/

section
open APFPaper1 APFPaper1.Source
variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
  [Fintype Record]

theorem source_hold_score_marks_p2mProof (w : Record → ℝ) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι' → D) (sigma : Equiv.Perm ι') (e d : ι') :
    holdScore (sourcePartyScore w maintained sufficient usesToRealize dist) sigma (markClass e)
        (markClass d) =
      sourcePartyScore w maintained sufficient usesToRealize dist (sigma.symm e) d :=
  holdScore_marks_p2mProof _ sigma e d

/-- For the ruled score: if a hold keeps it, reversing the two ends with the inverse hold in the channel
gives the same score. -/
theorem source_hold_ends_reversed_p2mProof (w : Record → ℝ) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : ι' → D) (sigma : Equiv.Perm ι')
    (hk : KeepsTable (sourcePartyScore w maintained sufficient usesToRealize dist) sigma)
    (x y : ι' → ℝ) :
    holdScore (sourcePartyScore w maintained sufficient usesToRealize dist) sigma x y =
      holdScore (sourcePartyScore w maintained sufficient usesToRealize dist) sigma.symm y x :=
  ends_reversed_of_keeps_p2mProof _ (sourcePartyScore_symm w maintained sufficient usesToRealize dist) sigma hk x y

end

end APFPaper5.K2


universe apfNative_uI
theorem solution :
∀ {ι : Type apfNative_uI} [inst : DecidableEq.{apfNative_uI + 1} ι] (sigma : Equiv.Perm.{apfNative_uI + 1} ι) (e : ι),
  @Eq.{apfNative_uI + 1} (ι → Real)
    (@APFPaper5.K2.heldAfter.{apfNative_uI} ι
      (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
        (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        sigma)
      (@APFPaper5.K1.markClass.{apfNative_uI} ι inst e))
    (@APFPaper5.K1.markClass.{apfNative_uI} ι inst
      (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
        (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
          (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι ι
          (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        (@Equiv.symm.{apfNative_uI + 1, apfNative_uI + 1} ι ι sigma) e)) := by
  exact @APFPaper5.K2.heldAfter_markClass_p2mProof
