-- Prove2me | solution 1 for APFPaper5.K2.holdScoreNull_before
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T20:49:47.397606+00:00
-- url     : https://prove2.me/submissions/a3e8e4fa-6429-40ae-ac74-3a01653eb7ee

import Definitions.Def_APFPaper5_K2_holds_keep_table_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_holds_keep_table
title: Holds keep K1's table: so a hold keeps the cost of every class, its reverse is its inverse, and the combinations of holds no score can see are closed under holds before, holds after and reversal
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
ruling: the author, 2026-11-15 13:23 HST, "yes, hold keeps table", in answer to this seat's question "Does a
 hold keep K1's table, meaning two distinctions score the same as the two they are rearranged from?"
 (RULING_hold_keeps_table_2026-11-15). From that time KeepsTable is an ADOPTED READING of a hold. It remains
 a hypothesis of every Lean theorem that uses it, and FOUNDATION_INPUTS is unchanged.
source: Paper 5 Supplement v7.33:410-420 (orientation closure), 723-737 and 790-811 (the metric adjoint; a
 score family that is context saturated and adjoint saturated has a two-sided adjoint-stable null ideal),
 866-890 (the quotient is an involutive algebra). Def_APFPaper5_K2_HoldScore, Thm_APFPaper5_K2_hold_score.
 This seat's Thm_APFPaper5_K1_identity_exchange (the ruled score of a counted family: symmetric, with a
 faithful nonnegative diagonal).
consumes_inputs: none. No declared input is used as a hypothesis and none is proved.
definition: HoldKeepsLedger G sigma, five statements about a rearrangement and a table: the hold keeps K1's
 form; the score through it is K1's form with the inverse on the test side; reversing the two ends with the
 inverse in the channel gives the same score; the cost of what it makes of any class is not negative; and
 is zero only for the zero class.
theorems:
 - (keepsTable_id, keepsTable_comp, keepsTable_symm) doing nothing keeps the table; two holds that keep it,
   one after the other, keep it; the inverse of one that keeps it keeps it.
 - (hold_keeps_cost) a hold that keeps the table keeps the cost of every class.
 - (holdScoreNull_before) a combination of holds no score can see stays unseen when one hold is put before
   every hold in it. No hypothesis.
 - (holdScoreNull_after_of_keeps) and when a hold that keeps the table is put after every hold in it.
 - (holdScoreNull_reverse_of_keeps) and, for a symmetric table and holds that keep it, when every hold in
   it is replaced by its inverse.
 - (hold_keeping_table_package) for a symmetric table with a faithful nonnegative diagonal, a hold that
   keeps it satisfies HoldKeepsLedger.
 - (source_counted_hold_package) so does a hold that keeps the ruled score of a counted family on source
   data of the declared forms, for any cost of records that is never negative.
reading: for holds, the combinations no score can see form what Paper 5 calls a two-sided adjoint-stable
 ideal, and the adjoint of a hold is its inverse. That is K2's involutive quotient, for holds.
not claimed:
 - That the adopted reading follows from the declared inputs. It is the author's reading of a hold.
 - That the reverse of a hold is an admitted word. The inverse rearrangement exists as a map of classes;
   whether a word of the world runs as it is not typed.
 - Anything about words that are not holds, or about sides. A side does not enter the score.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born is
   derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_id
import Theorems.Thm_APFPaper5_K2_rearrangesFamily_comp
import Theorems.Thm_APFPaper5_K2_nothingDrawn_of_rearranges
import Theorems.Thm_APFPaper5_K2_exists_rearranges_of_nothingDrawn
import Theorems.Thm_APFPaper5_K2_heldAfter_id
import Theorems.Thm_APFPaper5_K2_heldAfter_comp
import Theorems.Thm_APFPaper5_K2_heldAfter_add
import Theorems.Thm_APFPaper5_K2_heldAfter_smul
import Theorems.Thm_APFPaper5_K2_heldAfter_markClass
import Theorems.Thm_APFPaper5_K2_holdScore_id
import Theorems.Thm_APFPaper5_K2_holdScore_marks
import Theorems.Thm_APFPaper5_K2_holdScore_isBilinear
import Theorems.Thm_APFPaper5_K2_holdScore_eq_sum
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_of_keeps
import Theorems.Thm_APFPaper5_K2_keeps_of_reverse_is_inverse
import Theorems.Thm_APFPaper5_K2_reverse_is_inverse_iff_keeps
import Theorems.Thm_APFPaper5_K2_tableForm_heldAfter_of_keeps
import Theorems.Thm_APFPaper5_K2_ends_reversed_of_keeps
import Theorems.Thm_APFPaper5_K2_keepsTable_diag
import Theorems.Thm_APFPaper5_K2_not_keepsTable_of_diag_ne
import Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
import Theorems.Thm_APFPaper5_K2_source_hold_score_marks
import Theorems.Thm_APFPaper5_K2_source_hold_ends_reversed

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uK
variable {ι : Type uI}

/-! ### The holds that keep the table -/

theorem keepsTable_id_p2mProof (G : ι → ι → ℝ) : KeepsTable G id := fun _ _ => rfl

theorem keepsTable_comp_p2mProof (G : ι → ι → ℝ) (s₁ s₂ : ι → ι) (h₁ : KeepsTable G s₁)
    (h₂ : KeepsTable G s₂) : KeepsTable G (s₁ ∘ s₂) :=
  fun a b => (h₁ (s₂ a) (s₂ b)).trans (h₂ a b)

theorem keepsTable_symm_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (h : KeepsTable G sigma) :
    KeepsTable G sigma.symm := by
  intro a b
  have e := h (sigma.symm a) (sigma.symm b)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at e
  exact e.symm

section
variable [Fintype ι]

/-- A hold that keeps the table keeps the cost of every class. -/
theorem hold_keeps_cost_p2mProof (G : ι → ι → ℝ) (sigma : Equiv.Perm ι) (hk : KeepsTable G sigma)
    (x : ι → ℝ) : tableForm G (heldAfter sigma x) (heldAfter sigma x) = tableForm G x x :=
  tableForm_heldAfter_of_keeps G sigma hk x x

/-! ### The combinations no score can see, under holds before, holds after and reversal -/

theorem holdScoreNull_before_p2mProof {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
    (s : κ → ι → ι) (r : ι → ι) (h : HoldScoreNull G coef s) :
    HoldScoreNull G coef (fun k => r ∘ s k) :=
  fun x y => h (heldAfter r x) y

theorem holdScoreNull_after_of_keeps_p2mProof {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
    (s : κ → ι → ι) (t : Equiv.Perm ι) (hk : KeepsTable G t) (h : HoldScoreNull G coef s) :
    HoldScoreNull G coef (fun k => s k ∘ t) := by
  intro x y
  have e : ∀ k, holdScore G (s k ∘ t) x y = holdScore G (s k) x (heldAfter t.symm y) := by
    intro k
    exact reverse_is_inverse_of_keeps G t hk (heldAfter (s k) x) y
  simp only [e]
  exact h x (heldAfter t.symm y)

theorem holdScoreNull_reverse_of_keeps_p2mProof {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ)
    (hG : ∀ i j, G i j = G j i) (coef : κ → ℝ) (s : κ → Equiv.Perm ι)
    (hk : ∀ k, KeepsTable G (s k)) (h : HoldScoreNull G coef (fun k => (s k : ι → ι))) :
    HoldScoreNull G coef (fun k => ((s k).symm : ι → ι)) := by
  intro x y
  have e : ∀ k, holdScore G ((s k).symm : ι → ι) x y = holdScore G (s k) y x := by
    intro k
    exact (ends_reversed_of_keeps G hG (s k) (hk k) y x).symm
  simp only [e]
  exact h y x

/-! ### What the adopted reading gives, in one statement -/



theorem hold_keeping_table_package_p2mProof (G : ι → ι → ℝ) (hG : ∀ i j, G i j = G j i)
    (hf : FaithfulNonnegDiagonal (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G)
      (LinearEquiv.refl ℝ (ι → ℝ)))
    (sigma : Equiv.Perm ι) (hk : KeepsTable G sigma) : HoldKeepsLedger G sigma := by
  obtain ⟨hnn, hz⟩ := hf
  refine ⟨tableForm_heldAfter_of_keeps G sigma hk, reverse_is_inverse_of_keeps G sigma hk,
    ends_reversed_of_keeps G hG sigma hk, fun x => ?_, fun x hx => ?_⟩
  · rw [tableForm_heldAfter_of_keeps G sigma hk x x]
    exact hnn x
  · rw [tableForm_heldAfter_of_keeps G sigma hk x x] at hx
    exact hz x hx

end

/-! ### On source data of the declared forms, for the ruled score of a counted family -/

section
open APFPaper1 APFPaper1.Source
variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
  [Fintype Record]

theorem source_counted_hold_package_p2mProof (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a) (wholeResource : P → R)
    (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (tested : D → Prop) (C : ℝ) (dist : ι' → D)
    (h : SourceCounted w wholeResource calibration maintained sufficient usesToRealize tested C dist)
    (sigma : Equiv.Perm ι')
    (hk : KeepsTable (sourcePartyScore w maintained sufficient usesToRealize dist) sigma) :
    HoldKeepsLedger (sourcePartyScore w maintained sufficient usesToRealize dist) sigma :=
  hold_keeping_table_package_p2mProof _ (sourcePartyScore_symm w maintained sufficient usesToRealize dist)
    (source_counted_family_meets_all_of_K1_with_identity_exchange w hw wholeResource calibration
      maintained sufficient usesToRealize tested C dist h).2.2.2.1 sigma hk

end

end APFPaper5.K2


universe apfNative_uI apfNative_uK
theorem solution :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] {κ : Type apfNative_uK} [inst_1 : Fintype.{apfNative_uK} κ]
  (G : ι → ι → Real) (coef : κ → Real) (s : κ → ι → ι) (r : ι → ι)
  (h : @APFPaper5.K2.HoldScoreNull.{apfNative_uI, apfNative_uK} ι inst κ inst_1 G coef s),
  @APFPaper5.K2.HoldScoreNull.{apfNative_uI, apfNative_uK} ι inst κ inst_1 G coef fun (k : κ) =>
    @Function.comp.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} ι ι ι r (s k) := by
  exact @APFPaper5.K2.holdScoreNull_before_p2mProof
