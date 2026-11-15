-- Prove2me | solution 1 for APFPaper5.K4.compositeOnly_needs_own_record
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:25:02.374185+00:00
-- url     : https://prove2.me/submissions/d54ee777-ec1c-4bff-8309-f68a67c1df8b

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_composite_only_reading
title: With rates a joint reading is fixed by its values on products; without rates one joint reading is not, and it is the product of the two rates
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_CompositeOnly. The test agreed with the author on 2026-11-13.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition.
statement: (reading_zero_on_products_is_zero) a reading of the joint record book that is zero on every
 product is zero on every joint state.
 (compositeOnly_is_product_of_rates) on a product, the reading compositeOnly is minus twice the product of
 the two parts' rates.
 (compositeOnly_zero_on_rateFree_products, compositeOnly_on_recombination) so it is zero on every product of
 states with no rate, and it is one on a recombination of two such products.
 (rateFree_joint_state_fixed_by_parts_readings) for two joint states with no rate, written x and y: if the
 cost of AA', the cross terms of AA' with AB' and with BA', and the sum of the two cross terms across parts
 agree, the difference of the two cross terms across parts agrees as well.
 (sums_of_books_agree_on_parts_readings, sums_of_books_differ_in_compositeOnly) two pairs of joint states
 with no rate have the same total reading under every weighting that treats the two cross terms across
 parts alike, and different total readings under compositeOnly.
 (compositeOnly_needs_own_record) in a record model over pairs of joint states whose held records are fixed
 by such weightings of the total book, some reading of compositeOnly needs a record the family does not
 hold. Conditional on hsound, as in Thm_APFPaper5_K1_record_model_bridge.
reading: with rates, the joint record book is the parts' record books multiplied. Without rates it holds
 one reading more. A single joint state does not show the difference; a sum of two books does.
not_claimed: that record books of alternatives add; that a joint relation may hold no record of its own;
 hence no derivation of the rate. Any K.
-/
import Definitions.Def_APFPaper5_K4_CompositeOnly
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K1_needs_own_record_of_separates
import Theorems.Thm_APFPaper5_K1_recordModel_supportNovel_of_needs_own_record
import Theorems.Thm_APFPaper5_K1_recordModel_economy_of_separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

theorem reading_zero_on_products_is_zero (w : RecordWeights)
    (h0 : ∀ h k : Held2, linearRecord w (pair h k) = 0) (p : Joint) : linearRecord w p = 0 := by
  have i1 := h0 ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩
  have i2 := h0 ⟨1, 0, 0, 0⟩ ⟨0, 0, 1, 0⟩
  have i3 := h0 ⟨0, 0, 1, 0⟩ ⟨1, 0, 0, 0⟩
  have i4 := h0 ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩
  have j1 := h0 ⟨1, 0, 0, 0⟩ ⟨1, 0, 1, 0⟩
  have j2 := h0 ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 1⟩
  have j3 := h0 ⟨0, 0, 1, 0⟩ ⟨1, 0, 1, 0⟩
  have j4 := h0 ⟨0, 0, 1, 0⟩ ⟨1, 0, 0, 1⟩
  have j5 := h0 ⟨1, 0, 1, 0⟩ ⟨1, 0, 0, 0⟩
  have j6 := h0 ⟨1, 0, 0, 1⟩ ⟨1, 0, 0, 0⟩
  have j7 := h0 ⟨1, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩
  have j8 := h0 ⟨1, 0, 0, 1⟩ ⟨0, 0, 1, 0⟩
  have k1 := h0 ⟨1, 0, 1, 0⟩ ⟨1, 0, 1, 0⟩
  have k2 := h0 ⟨1, 0, 0, 1⟩ ⟨1, 0, 0, 1⟩
  have k3 := h0 ⟨1, 0, 1, 0⟩ ⟨1, 0, 0, 1⟩
  have k4 := h0 ⟨1, 0, 0, 1⟩ ⟨1, 0, 1, 0⟩
  dsimp only [linearRecord, pair] at i1 i2 i3 i4 j1 j2 j3 j4 j5 j6 j7 j8 k1 k2 k3 k4
  norm_num at i1 i2 i3 i4 j1 j2 j3 j4 j5 j6 j7 j8 k1 k2 k3 k4
  have f1 : w.d1 = 0 := by linarith
  have f2 : w.d2 = 0 := by linarith
  have f3 : w.d3 = 0 := by linarith
  have f4 : w.d4 = 0 := by linarith
  have f5 : w.u12 = 0 := by linarith
  have f6 : w.v12 = 0 := by linarith
  have f7 : w.u34 = 0 := by linarith
  have f8 : w.v34 = 0 := by linarith
  have f9 : w.u13 = 0 := by linarith
  have f10 : w.v13 = 0 := by linarith
  have f11 : w.u24 = 0 := by linarith
  have f12 : w.v24 = 0 := by linarith
  have f13 : w.u14 = 0 := by linarith
  have f14 : w.u23 = 0 := by linarith
  have f15 : w.v14 = 0 := by linarith
  have f16 : w.v23 = 0 := by linarith
  dsimp only [linearRecord]
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16]
  ring

theorem compositeOnly_is_product_of_rates (h k : Held2) :
    linearRecord compositeOnly (pair h k) = -2 * crossIm h * crossIm k := by
  dsimp only [linearRecord, compositeOnly, pair, crossIm]
  ring

theorem compositeOnly_zero_on_rateFree_products (h k : Held2) (hh : RateFree h) :
    linearRecord compositeOnly (pair h k) = 0 := by
  rw [compositeOnly_is_product_of_rates]
  dsimp only [crossIm]
  rw [hh.1, hh.2]
  ring

theorem compositeOnly_on_recombination :
    linearRecord compositeOnly
      (jointAdd (pair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨0, 0, 1, 0⟩)) = 1 := by
  dsimp only [linearRecord, compositeOnly, jointAdd, pair]
  norm_num

theorem rateFree_joint_state_fixed_by_parts_readings (x1 x2 x3 x4 y1 y2 y3 y4 : ℝ)
    (c1 : x1 * x1 = y1 * y1) (h12 : x1 * x2 = y1 * y2) (h13 : x1 * x3 = y1 * y3)
    (hsum : x1 * x4 + x2 * x3 = y1 * y4 + y2 * y3) :
    x1 * x4 - x2 * x3 = y1 * y4 - y2 * y3 := by
  have hr : (x1 * x1) * (x2 * x3 - y2 * y3) = 0 := by
    linear_combination x1 * x3 * h12 + y1 * y2 * h13 - y2 * y3 * c1
  rcases mul_eq_zero.mp hr with hx | hx
  · have hx1 : x1 = 0 := mul_self_eq_zero.mp hx
    have hy1 : y1 = 0 := by
      rw [hx1] at c1
      exact mul_self_eq_zero.mp (by linarith)
    rw [hx1, hy1] at hsum ⊢
    linarith
  · linarith

theorem sums_of_books_agree_on_parts_readings (w : RecordWeights) (hw : w.u14 = w.u23) :
    linearRecord w ⟨1, 0, 0, 0, 0, 0, -1, 0⟩ + linearRecord w ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ =
      linearRecord w ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ + linearRecord w ⟨0, 0, 1, 0, -1, 0, 0, 0⟩ := by
  dsimp only [linearRecord]
  linear_combination (-2 : ℝ) * hw

theorem sums_of_books_differ_in_compositeOnly :
    linearRecord compositeOnly ⟨1, 0, 0, 0, 0, 0, -1, 0⟩ +
        linearRecord compositeOnly ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = -2 ∧
      linearRecord compositeOnly ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ +
        linearRecord compositeOnly ⟨0, 0, 1, 0, -1, 0, 0, 0⟩ = 2 := by
  constructor <;> dsimp only [linearRecord, compositeOnly] <;> norm_num

theorem compositeOnly_needs_own_record {ι : Type*} {Rec : Type*} [DecidableEq Rec] {Val : Type*}
    (fam : ι → Finset Rec) (reads : Rec → Joint × Joint → Val)
    (verdict : ι → Joint × Joint → Prop) (S : Finset ι)
    (hS : ∀ r ∈ S.biUnion fam, ∀ x y : Joint × Joint,
      (∀ w : RecordWeights, w.u14 = w.u23 →
        linearRecord w x.1 + linearRecord w x.2 = linearRecord w y.1 + linearRecord w y.2) →
      reads r x = reads r y)
    (dComp : ℝ → ι)
    (hverdict : ∀ (t : ℝ) (x : Joint × Joint), verdict (dComp t) x ↔
      linearRecord compositeOnly x.1 + linearRecord compositeOnly x.2 = t)
    (hsound : ∀ (t : ℝ) (x y : Joint × Joint), (∀ r ∈ fam (dComp t), reads r x = reads r y) →
      (verdict (dComp t) x ↔ verdict (dComp t) y)) :
    ∃ t : ℝ, ¬ fam (dComp t) ⊆ S.biUnion fam := by
  obtain ⟨hm, hp⟩ := sums_of_books_differ_in_compositeOnly
  refine ⟨-2, APFPaper5.K1.needs_own_record_of_separates fam reads verdict S _ (hsound (-2))
    (⟨1, 0, 0, 0, 0, 0, -1, 0⟩, ⟨0, 0, 1, 0, 1, 0, 0, 0⟩)
    (⟨1, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 0, -1, 0, 0, 0⟩)
    (fun r hr => hS r hr _ _ (fun w hw => sums_of_books_agree_on_parts_readings w hw)) ?_⟩
  rw [hverdict, hverdict]
  intro hiff
  have h2 := hiff.mp hm
  rw [hp] at h2
  norm_num at h2

end APFPaper5.K4


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {ι : Type apfNative_u_1} {Rec : Type apfNative_u_2} [inst : DecidableEq.{apfNative_u_2 + 1} Rec]
  {Val : Type apfNative_u_3} (fam : ι → Finset.{apfNative_u_2} Rec)
  (reads : Rec → Prod.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint → Val)
  (verdict : ι → Prod.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint → Prop) (S : Finset.{apfNative_u_1} ι)
  (hS :
    ∀ (r : Rec),
      @Membership.mem.{apfNative_u_2, apfNative_u_2} Rec (Finset.{apfNative_u_2} Rec)
          (@SetLike.instMembership.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} Rec) Rec
            (@Finset.instSetLike.{apfNative_u_2} Rec))
          (@Finset.biUnion.{apfNative_u_1, apfNative_u_2} ι Rec inst S fam) r →
        ∀ (x y : Prod.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint),
          (∀ (w : APFPaper5.K4.RecordWeights),
              @Eq.{1} Real (APFPaper5.K4.RecordWeights.u14 w) (APFPaper5.K4.RecordWeights.u23 w) →
                @Eq.{1} Real
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (APFPaper5.K4.linearRecord w (@Prod.fst.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint x))
                    (APFPaper5.K4.linearRecord w (@Prod.snd.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint x)))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (APFPaper5.K4.linearRecord w (@Prod.fst.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint y))
                    (APFPaper5.K4.linearRecord w (@Prod.snd.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint y)))) →
            @Eq.{apfNative_u_3 + 1} Val (reads r x) (reads r y))
  (dComp : Real → ι)
  (hverdict :
    ∀ (t : Real) (x : Prod.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint),
      Iff (verdict (dComp t) x)
        (@Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (APFPaper5.K4.linearRecord APFPaper5.K4.compositeOnly
              (@Prod.fst.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint x))
            (APFPaper5.K4.linearRecord APFPaper5.K4.compositeOnly
              (@Prod.snd.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint x)))
          t))
  (hsound :
    ∀ (t : Real) (x y : Prod.{0, 0} APFPaper5.K4.Joint APFPaper5.K4.Joint),
      (∀ (r : Rec),
          @Membership.mem.{apfNative_u_2, apfNative_u_2} Rec (Finset.{apfNative_u_2} Rec)
              (@SetLike.instMembership.{apfNative_u_2, apfNative_u_2} (Finset.{apfNative_u_2} Rec) Rec
                (@Finset.instSetLike.{apfNative_u_2} Rec))
              (fam (dComp t)) r →
            @Eq.{apfNative_u_3 + 1} Val (reads r x) (reads r y)) →
        Iff (verdict (dComp t) x) (verdict (dComp t) y)),
  @Exists.{1} Real fun (t : Real) =>
    Not
      (@LE.le.{apfNative_u_2} (Finset.{apfNative_u_2} Rec)
        (@Preorder.toLE.{apfNative_u_2} (Finset.{apfNative_u_2} Rec)
          (@PartialOrder.toPreorder.{apfNative_u_2} (Finset.{apfNative_u_2} Rec)
            (@Finset.instPartialOrder.{apfNative_u_2} Rec)))
        (fam (dComp t)) (@Finset.biUnion.{apfNative_u_1, apfNative_u_2} ι Rec inst S fam)) := by
  exact @APFPaper5.K4.compositeOnly_needs_own_record
