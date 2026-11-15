-- Prove2me | solution 1 for APFPaper5.K4.rateFlip_does_not_extend
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:56:31.628668+00:00
-- url     : https://prove2.me/submissions/ec5fe475-73c2-4d7e-b7c6-1176dfd45cc5

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_flipped_part
title: On a joint carrier, a reading that is linear in the joint record book and reads on products as the rate flip of one part takes the value minus two on a joint state
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_JointCarrier. Author's ruling of 2026-11-13: route C.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition.
statement: (pair_quarter_left, pair_quarter_right) a quarter turn of either part is the quarter turn of the
 joint state: the two parts share one quarter turn.
 (pair_flip_both, jointFlip_recDiag) the rate flip of both parts is the rate flip of the joint state, and
 leaves the cost recDiag unchanged.
 (antisym_is_recombination) antisym is one product minus another.
 (recDiag_nonneg, recDiag_is_linearRecord) recDiag is nonnegative and linear in the joint record book.
 (flipped_part_record_on_products) one explicit reading, linear in the joint record book, equals on every
 product the cost recDiag after the rate flip of the first part.
 (flipped_part_record_value) every reading that is linear in the joint record book and does so takes the
 value minus two on antisym.
 (no_nonneg_flipped_part_record) so no such reading is nonnegative on every joint state.
 (rateFlip_does_not_extend) the rate flip does not extend to joint states.
 (identity_extends) the identity does.
reading: a cost is nonnegative. A process that flips one part and acts on the joint record book additively
 would produce a cost of minus two. Flipping everything at once produces no such thing.
not_claimed: that composites at an interface are this carrier; that every admitted map of a part extends to
 joint states; that processes act on the record book additively; the composition clause; any K.
-/
import Definitions.Def_APFPaper5_K4_JointCarrier
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

theorem pair_quarter_left (h k : Held2) : pair (commonTurn 0 1 h) k = jointQuarter (pair h k) := by
  apply Joint.ext <;> dsimp only [pair, commonTurn, jointQuarter] <;> ring

theorem pair_quarter_right (h k : Held2) : pair h (commonTurn 0 1 k) = jointQuarter (pair h k) := by
  apply Joint.ext <;> dsimp only [pair, commonTurn, jointQuarter] <;> ring

theorem pair_flip_both (h k : Held2) : pair (rateFlip h) (rateFlip k) = jointFlip (pair h k) := by
  apply Joint.ext <;> dsimp only [pair, rateFlip, jointFlip] <;> ring

theorem jointFlip_recDiag (p : Joint) : recDiag (jointFlip p) = recDiag p := by
  dsimp only [recDiag, jointFlip]
  ring

theorem antisym_is_recombination :
    antisym = jointSub (pair ⟨1, 0, 0, 0⟩ ⟨0, 0, 1, 0⟩) (pair ⟨0, 0, 1, 0⟩ ⟨1, 0, 0, 0⟩) := by
  apply Joint.ext <;> dsimp only [antisym, jointSub, pair] <;> norm_num

theorem recDiag_nonneg (p : Joint) : 0 ≤ recDiag p :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem recDiag_is_linearRecord (p : Joint) :
    recDiag p = linearRecord ⟨1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩ p := by
  dsimp only [recDiag, linearRecord]
  ring

theorem flipped_part_record_on_products (h k : Held2) :
    linearRecord ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩ (pair h k) =
      recDiag (pair (rateFlip h) k) := by
  dsimp only [recDiag, linearRecord, pair, rateFlip]
  ring

theorem flipped_part_record_value (w : RecordWeights)
    (hprod : ∀ h k : Held2, linearRecord w (pair h k) = recDiag (pair (rateFlip h) k)) :
    linearRecord w antisym = -2 := by
  have i1 := hprod ⟨1, 0, 0, 0⟩ ⟨0, 0, 1, 0⟩
  have i2 := hprod ⟨0, 0, 1, 0⟩ ⟨1, 0, 0, 0⟩
  have e1 := hprod ⟨1, 0, 1, 0⟩ ⟨1, 0, 1, 0⟩
  have e2 := hprod ⟨1, 0, 0, 1⟩ ⟨1, 0, 0, 1⟩
  have e3 := hprod ⟨1, 0, -1, 0⟩ ⟨1, 0, -1, 0⟩
  have e4 := hprod ⟨1, 0, 0, -1⟩ ⟨1, 0, 0, -1⟩
  have e5 := hprod ⟨1, 0, -1, 0⟩ ⟨1, 0, 1, 0⟩
  have e6 := hprod ⟨1, 0, 0, -1⟩ ⟨1, 0, 0, 1⟩
  have e7 := hprod ⟨1, 0, 1, 0⟩ ⟨1, 0, -1, 0⟩
  have e8 := hprod ⟨1, 0, 0, 1⟩ ⟨1, 0, 0, -1⟩
  dsimp only [linearRecord, pair, recDiag, rateFlip] at i1 i2 e1 e2 e3 e4 e5 e6 e7 e8
  dsimp only [linearRecord, antisym]
  linear_combination i1 + i2 - (1 / 8) * (e1 + e2 + e3 + e4 - e5 - e6 - e7 - e8)

theorem no_nonneg_flipped_part_record :
    ¬ ∃ w : RecordWeights,
      (∀ h k : Held2, linearRecord w (pair h k) = recDiag (pair (rateFlip h) k)) ∧
        ∀ p : Joint, 0 ≤ linearRecord w p := by
  rintro ⟨w, hprod, hpos⟩
  have hv := flipped_part_record_value w hprod
  have hp := hpos antisym
  linarith

theorem rateFlip_does_not_extend : ¬ ExtendsToJoint rateFlip := by
  rintro ⟨F, w, hlin, hprod⟩
  have hv := flipped_part_record_value w (fun h k => (hlin (pair h k)).symm.trans (hprod h k))
  have hp := recDiag_nonneg (F antisym)
  rw [hlin antisym] at hp
  linarith

theorem identity_extends : ExtendsToJoint (fun h : Held2 => h) :=
  ⟨fun p => p, ⟨1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0⟩, recDiag_is_linearRecord,
    fun _ _ => rfl⟩

end APFPaper5.K4


theorem solution :
Not (APFPaper5.K4.ExtendsToJoint APFPaper5.K3.rateFlip) := by
  exact @APFPaper5.K4.rateFlip_does_not_extend
