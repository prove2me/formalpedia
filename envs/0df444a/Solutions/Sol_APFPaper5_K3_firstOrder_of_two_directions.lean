-- Prove2me | solution 1 for APFPaper5.K3.firstOrder_of_two_directions
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:37:16.610463+00:00
-- url     : https://prove2.me/submissions/891fa593-745d-4960-ab11-80ffdcc168e5

import Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_firstOrder_economy
title: The first-order relation is "two directions and no more": two are needed, and what the readings exclude is in each case structure that separates more
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ruling of 2026-11-12 naming the first-order clause; DECISION_first_order_readings_2026-11-13; the
 author's question "Can we derive it". Paper 5 Supplement v7.33:1494 ("the minimum complete represented local
 continuation-germ carrier"), 1621-1650, 1956 ("rank two is first-order minimality").
consumes_inputs: none. General statements, and CONDITIONAL INSTANCES in the supplied models.
statement: (firstOrder_of_two_directions) if every held state is a combination of z and its turn, the
 first-order relation holds for that turn at z.
 (two_directions_needed) if a turn leaves the cross term of cost unchanged and the number between z and its
 turn is neither the cost of z nor its reverse, then z and its turn are independent.
 (seen_common_turn_splits_an_object) if the common turn is seen after a map, two held states with the same
 continuation profile have different continuation profiles after it.
 (APFPaper5.K4.mirror_reading_on_products) every reading of the mirror sheet's record book, on a product, is
 a reading of the first sheet's record book.
 (APFPaper5.K4.two_sheets_separate_more) two two-sheet states agree on the first sheet and differ in a
 reading.
reading: the first-order clause says the relation uses two directions, the least that will do. Each of the
 two readings put to the author excludes structure that separates more states than the required records do.
not_claimed: that the extra structure is a support-novel distinction in the sense of B05; that the smaller
 structure is admissible; hence no derivation of the first-order clause from the declared inputs.
-/
import Definitions.Def_APFPaper5_K3_FirstOrder
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3

open APFPaper5.K1

theorem firstOrder_of_two_directions {V : Type*} [AddCommGroup V] [Module ℝ V] (T : V → V) (z : V)
    (hspan : ∀ v : V, ∃ a b : ℝ, v = a • z + b • T z) : FirstOrder T z :=
  hspan (T (T z))

theorem two_directions_needed {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V → V → ℝ)
    (hB : IsBilinear B) (hsym : ∀ x y : V, B x y = B y x) (T : V → V)
    (hT : ∀ x y : V, B (T x) (T y) = B x y) (z : V)
    (hne : B z (T z) * B z (T z) ≠ B z z * B z z) :
    ∀ a b : ℝ, a • z + b • T z = 0 → a = 0 ∧ b = 0 := by
  obtain ⟨_, _, h3, h4⟩ := hB
  intro a b h0
  have hz0 : ∀ x : V, B x 0 = 0 := by
    intro x
    have e := h4 0 x x
    rwa [zero_smul, zero_mul] at e
  have e1 : a * B z z + b * B z (T z) = 0 := by
    have e := congrArg (B z) h0
    rw [h3, h4, h4, hz0] at e
    exact e
  have e2 : a * B z (T z) + b * B z z = 0 := by
    have e := congrArg (B (T z)) h0
    rw [h3, h4, h4, hz0, hsym (T z) z, hT] at e
    exact e
  have hd : B z z * B z z - B z (T z) * B z (T z) ≠ 0 := by
    intro hd0
    apply hne
    linarith
  have ha : a * (B z z * B z z - B z (T z) * B z (T z)) = 0 := by
    linear_combination B z z * e1 - B z (T z) * e2
  have hb : b * (B z z * B z z - B z (T z) * B z (T z)) = 0 := by
    linear_combination B z z * e2 - B z (T z) * e1
  exact ⟨(mul_eq_zero.mp ha).resolve_right hd, (mul_eq_zero.mp hb).resolve_right hd⟩

theorem seen_common_turn_splits_an_object (T : Held2 → Held2) (hseen : ¬ CommonTurnUnseenAfter T) :
    ∃ x y : Held2, plainAfterTurn x = plainAfterTurn y ∧
      plainAfterTurn (T x) ≠ plainAfterTurn (T y) := by
  obtain ⟨c, hc⟩ := not_forall.mp hseen
  obtain ⟨s, hs⟩ := not_forall.mp hc
  obtain ⟨hcs, hrest⟩ := Classical.not_imp.mp hs
  obtain ⟨h, hh⟩ := not_forall.mp hrest
  exact ⟨commonTurn c s h, h, plainAfterTurn_commonTurn c s hcs h, hh⟩

end APFPaper5.K3

namespace APFPaper5.K4

open APFPaper5.K3

theorem mirror_reading_on_products (w : RecordWeights) (h k : Held2) :
    linearRecord w (pairAnti h k) = linearRecord (transposeSecond w) (pair h k) := by
  dsimp only [linearRecord, transposeSecond, pairAnti, pair, rateFlip]
  ring

theorem two_sheets_separate_more :
    ∃ p q : Sheets, p.sync = q.sync ∧
      ∃ w w' : RecordWeights, sheetsReading w w' p ≠ sheetsReading w w' q := by
  refine ⟨⟨jointZero, ⟨1, 0, 0, 0, 0, 0, 0, 0⟩⟩, ⟨jointZero, jointZero⟩, rfl,
    ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ?_⟩
  dsimp only [sheetsReading, linearRecord, jointZero]
  norm_num

end APFPaper5.K4


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (T : V → V) (z : V)
  (hspan :
    ∀ (v : V),
      @Exists.{1} Real fun (a : Real) =>
        @Exists.{1} Real fun (b : Real) =>
          @Eq.{apfNative_u_1 + 1} V v
            (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
              (@instHAdd.{apfNative_u_1} V
                (@AddCommMagma.toAdd.{apfNative_u_1} V
                  (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                    (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                      (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
              (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
                (@instHSMul.{0, apfNative_u_1} Real V
                  (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                    (@AddZero.toZero.{apfNative_u_1} V
                      (@AddZeroClass.toAddZero.{apfNative_u_1} V
                        (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                    (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                      (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                        (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
                a z)
              (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
                (@instHSMul.{0, apfNative_u_1} Real V
                  (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                    (@AddZero.toZero.{apfNative_u_1} V
                      (@AddZeroClass.toAddZero.{apfNative_u_1} V
                        (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                    (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                      (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                        (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
                b (T z)))),
  @APFPaper5.K3.FirstOrder.{apfNative_u_1} V inst inst_1 T z := by
  exact @APFPaper5.K3.firstOrder_of_two_directions
