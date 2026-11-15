-- Prove2me | solution 1 for APFPaper5.K4.one_sheet_of_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:06:10.626943+00:00
-- url     : https://prove2.me/submissions/9bfd32ab-ad55-4644-9fac-1ae2607bfb2f

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_mirror_sheet
title: On the two-sheet joint carrier a turn of either part is unseen yet the parts share no quarter turn; the first-order clause for the turn of both parts leaves one sheet; the other sheet is the first with one part's rates reversed
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_TwoSheets.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition.
statement: (pair_turn_left, pair_turn_right, pairAnti_turn_left, pairAnti_turn_right) on the product a turn of
 either part is the same turn of the joint state; on the mirror product a turn of the second part is the
 opposite turn.
 (sync_coturn, anti_coturn) when both parts turn together the product turns by the sum and the mirror
 product does not turn.
 (flipped_first_is_mirror, recDiag_flipped_first) the product with the first part's rates reversed is the
 mirror product with every rate reversed, and has the same cost recDiag.
 (mirror_cost_is_no_reading_of_the_product_book) the mirror sheet's cost recDiag is no nonnegative reading
 of the first sheet's record book.
 (sheetsPair_turnFirst, sheetsPair_turnSecond, sheetsReading_turnFirst, sheetsReading_turnSecond,
 turns_of_the_parts_differ) on the two-sheet carrier every reading is unchanged by a turn of either part,
 and the two quarter turns differ.
 (sheetsPair_coTurn) turning both parts of a product is coTurn.
 (one_sheet_of_firstOrder) a two-sheet state at which the first-order relation holds for coTurn lies on one
 sheet. (product_violates_firstOrder) a product of the two-sheet carrier does not.
 (one_sheet_firstOrder_holds) on one sheet the relation holds at every joint state.
 (all_on_one_sheet) if the held joint states are closed under recombination and the relation holds at each,
 they all lie on the same sheet.
reading: unseen turns of the parts do not force one shared quarter turn. The first-order clause, read for
 the turn of both parts together, does, up to which direction of the second part is called forward.
not_claimed: that the first-order clause applies to the turn of both parts at an interface; that composites
 there are either carrier; the composition clause; any K.
-/
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

theorem pair_turn_left (c s : ℝ) (h k : Held2) :
    pair (commonTurn c s h) k = jointTurn c s (pair h k) := by
  apply Joint.ext <;> dsimp only [pair, commonTurn, jointTurn] <;> ring

theorem pair_turn_right (c s : ℝ) (h k : Held2) :
    pair h (commonTurn c s k) = jointTurn c s (pair h k) := by
  apply Joint.ext <;> dsimp only [pair, commonTurn, jointTurn] <;> ring

theorem pairAnti_turn_left (c s : ℝ) (h k : Held2) :
    pairAnti (commonTurn c s h) k = jointTurn c s (pairAnti h k) :=
  pair_turn_left c s h (rateFlip k)

theorem pairAnti_turn_right (c s : ℝ) (h k : Held2) :
    pairAnti h (commonTurn c s k) = jointTurn c (-s) (pairAnti h k) := by
  apply Joint.ext <;> dsimp only [pairAnti, pair, rateFlip, commonTurn, jointTurn] <;> ring

theorem jointTurn_comp (c s c' s' : ℝ) (p : Joint) :
    jointTurn c s (jointTurn c' s' p) = jointTurn (c * c' - s * s') (c * s' + s * c') p := by
  apply Joint.ext <;> dsimp only [jointTurn] <;> ring

theorem jointTurn_one_zero (p : Joint) : jointTurn 1 0 p = p := by
  apply Joint.ext <;> dsimp only [jointTurn] <;> ring

theorem sync_coturn (c s : ℝ) (h k : Held2) :
    pair (commonTurn c s h) (commonTurn c s k) =
      jointTurn (c * c - s * s) (c * s + s * c) (pair h k) := by
  rw [pair_turn_left, pair_turn_right, jointTurn_comp]

theorem anti_coturn (c s : ℝ) (hcs : c * c + s * s = 1) (h k : Held2) :
    pairAnti (commonTurn c s h) (commonTurn c s k) = pairAnti h k := by
  have e1 : c * c - s * -s = 1 := by linear_combination hcs
  have e2 : c * -s + s * c = 0 := by ring
  rw [pairAnti_turn_left, pairAnti_turn_right, jointTurn_comp, e1, e2, jointTurn_one_zero]

theorem flipped_first_is_mirror (h k : Held2) :
    pair (rateFlip h) k = jointFlip (pairAnti h k) := by
  apply Joint.ext <;> dsimp only [pairAnti, pair, rateFlip, jointFlip] <;> ring

theorem recDiag_flipped_first (h k : Held2) :
    recDiag (pair (rateFlip h) k) = recDiag (pairAnti h k) := by
  rw [flipped_first_is_mirror, jointFlip_recDiag]

theorem mirror_cost_is_no_reading_of_the_product_book :
    ¬ ∃ w : RecordWeights,
      (∀ h k : Held2, linearRecord w (pair h k) = recDiag (pairAnti h k)) ∧
        ∀ p : Joint, 0 ≤ linearRecord w p := by
  rintro ⟨w, hprod, hpos⟩
  exact no_nonneg_flipped_part_record
    ⟨w, fun h k => (hprod h k).trans (recDiag_flipped_first h k).symm, hpos⟩

theorem linearRecord_jointTurn (w : RecordWeights) (c s : ℝ) (hcs : c * c + s * s = 1)
    (p : Joint) : linearRecord w (jointTurn c s p) = linearRecord w p := by
  have e : linearRecord w (jointTurn c s p) = (c * c + s * s) * linearRecord w p := by
    dsimp only [linearRecord, jointTurn]
    ring
  rw [e, hcs, one_mul]

theorem sheetsPair_turnFirst (c s : ℝ) (h k : Held2) :
    sheetsPair (commonTurn c s h) k = turnFirstBy c s (sheetsPair h k) :=
  Sheets.ext (pair_turn_left c s h k) (pairAnti_turn_left c s h k)

theorem sheetsPair_turnSecond (c s : ℝ) (h k : Held2) :
    sheetsPair h (commonTurn c s k) = turnSecondBy c s (sheetsPair h k) :=
  Sheets.ext (pair_turn_right c s h k) (pairAnti_turn_right c s h k)

theorem sheetsReading_turnFirst (w w' : RecordWeights) (c s : ℝ) (hcs : c * c + s * s = 1)
    (p : Sheets) : sheetsReading w w' (turnFirstBy c s p) = sheetsReading w w' p := by
  dsimp only [sheetsReading, turnFirstBy]
  rw [linearRecord_jointTurn w c s hcs, linearRecord_jointTurn w' c s hcs]

theorem sheetsReading_turnSecond (w w' : RecordWeights) (c s : ℝ) (hcs : c * c + s * s = 1)
    (p : Sheets) : sheetsReading w w' (turnSecondBy c s p) = sheetsReading w w' p := by
  dsimp only [sheetsReading, turnSecondBy]
  rw [linearRecord_jointTurn w c s hcs,
    linearRecord_jointTurn w' c (-s) (by linear_combination hcs)]

theorem turns_of_the_parts_differ :
    turnFirstBy 0 1 (sheetsPair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) ≠
      turnSecondBy 0 1 (sheetsPair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩) := by
  intro h
  have h2 := congrArg (fun p : Sheets => p.anti.y1) h
  dsimp only [turnFirstBy, turnSecondBy, sheetsPair, pairAnti, pair, rateFlip, jointTurn] at h2
  norm_num at h2

theorem sheetsPair_coTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h k : Held2) :
    sheetsPair (commonTurn c s h) (commonTurn c s k) =
      coTurn (c * c - s * s) (c * s + s * c) (sheetsPair h k) :=
  Sheets.ext (sync_coturn c s h k) (anti_coturn c s hcs h k)

theorem one_sheet_of_firstOrder (C S : ℝ) (hCS : C * C + S * S = 1) (hS : S ≠ 0) (p : Sheets)
    (hfo : ∃ α β : ℝ, coTurn C S (coTurn C S p) =
      sheetsAdd (sheetsSmul α p) (sheetsSmul β (coTurn C S p))) :
    p.sync = jointZero ∨ p.anti = jointZero := by
  obtain ⟨α, β, h⟩ := hfo
  obtain ⟨x, a⟩ := p
  obtain ⟨x1, y1, x2, y2, x3, y3, x4, y4⟩ := x
  obtain ⟨a1, b1, a2, b2, a3, b3, a4, b4⟩ := a
  have hs := congrArg Sheets.sync h
  have ha := congrArg Sheets.anti h
  dsimp only [coTurn, sheetsAdd, sheetsSmul] at hs ha
  have s1 := congrArg Joint.x1 hs
  have s2 := congrArg Joint.y1 hs
  have s3 := congrArg Joint.x2 hs
  have s4 := congrArg Joint.y2 hs
  have s5 := congrArg Joint.x3 hs
  have s6 := congrArg Joint.y3 hs
  have s7 := congrArg Joint.x4 hs
  have s8 := congrArg Joint.y4 hs
  have t1 := congrArg Joint.x1 ha
  have t2 := congrArg Joint.y1 ha
  have t3 := congrArg Joint.x2 ha
  have t4 := congrArg Joint.y2 ha
  have t5 := congrArg Joint.x3 ha
  have t6 := congrArg Joint.y3 ha
  have t7 := congrArg Joint.x4 ha
  have t8 := congrArg Joint.y4 ha
  dsimp only [jointTurn, jointAdd, jointSmul] at s1 s2 s3 s4 s5 s6 s7 s8 t1 t2 t3 t4 t5 t6 t7 t8
  have key : ((C * C - S * S - α - β * C) * (C * C - S * S - α - β * C) +
      (2 * C * S - β * S) * (2 * C * S - β * S)) *
      (x1 * x1 + y1 * y1 + x2 * x2 + y2 * y2 + x3 * x3 + y3 * y3 + x4 * x4 + y4 * y4) = 0 := by
    linear_combination
      ((C * C - S * S - α - β * C) * x1 - (2 * C * S - β * S) * y1) * s1 +
      ((2 * C * S - β * S) * x1 + (C * C - S * S - α - β * C) * y1) * s2 +
      ((C * C - S * S - α - β * C) * x2 - (2 * C * S - β * S) * y2) * s3 +
      ((2 * C * S - β * S) * x2 + (C * C - S * S - α - β * C) * y2) * s4 +
      ((C * C - S * S - α - β * C) * x3 - (2 * C * S - β * S) * y3) * s5 +
      ((2 * C * S - β * S) * x3 + (C * C - S * S - α - β * C) * y3) * s6 +
      ((C * C - S * S - α - β * C) * x4 - (2 * C * S - β * S) * y4) * s7 +
      ((2 * C * S - β * S) * x4 + (C * C - S * S - α - β * C) * y4) * s8
  rcases mul_eq_zero.mp key with huv | hcost
  · obtain ⟨hu, hv⟩ := mul_self_add_mul_self_eq_zero.mp huv
    have hβ : β = 2 * C := by
      have hS' : S * (2 * C - β) = 0 := by linear_combination hv
      rcases mul_eq_zero.mp hS' with h0 | h0
      · exact absurd h0 hS
      · linarith
    have hα : α = -1 := by
      rw [hβ] at hu
      linear_combination -hu - hCS
    have hC : C - 1 ≠ 0 := by
      intro h1
      apply hS
      have hC1 : C = 1 := by linarith
      rw [hC1] at hCS
      exact mul_self_eq_zero.mp (by linarith)
    have kill : ∀ z : ℝ, z = α * z + β * z → z = 0 := by
      intro z hz
      rw [hα, hβ] at hz
      have hz' : (C - 1) * z = 0 := by linear_combination (-1 / 2) * hz
      rcases mul_eq_zero.mp hz' with h0 | h0
      · exact absurd h0 hC
      · exact h0
    exact Or.inr (Joint.ext (kill _ t1) (kill _ t2) (kill _ t3) (kill _ t4) (kill _ t5)
      (kill _ t6) (kill _ t7) (kill _ t8))
  · have n1 := mul_self_nonneg x1
    have n2 := mul_self_nonneg y1
    have n3 := mul_self_nonneg x2
    have n4 := mul_self_nonneg y2
    have n5 := mul_self_nonneg x3
    have n6 := mul_self_nonneg y3
    have n7 := mul_self_nonneg x4
    have n8 := mul_self_nonneg y4
    exact Or.inl (Joint.ext (mul_self_eq_zero.mp (by linarith)) (mul_self_eq_zero.mp (by linarith))
      (mul_self_eq_zero.mp (by linarith)) (mul_self_eq_zero.mp (by linarith))
      (mul_self_eq_zero.mp (by linarith)) (mul_self_eq_zero.mp (by linarith))
      (mul_self_eq_zero.mp (by linarith)) (mul_self_eq_zero.mp (by linarith)))

theorem product_violates_firstOrder (C S : ℝ) (hCS : C * C + S * S = 1) (hS : S ≠ 0) :
    ¬ ∃ α β : ℝ, coTurn C S (coTurn C S (sheetsPair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩)) =
      sheetsAdd (sheetsSmul α (sheetsPair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩))
        (sheetsSmul β (coTurn C S (sheetsPair ⟨1, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩))) := by
  intro hfo
  rcases one_sheet_of_firstOrder C S hCS hS _ hfo with h0 | h0
  · have h1 := congrArg Joint.x1 h0
    dsimp only [sheetsPair, pair, jointZero] at h1
    norm_num at h1
  · have h1 := congrArg Joint.x1 h0
    dsimp only [sheetsPair, pairAnti, pair, rateFlip, jointZero] at h1
    norm_num at h1

theorem one_sheet_firstOrder_holds (C S : ℝ) (hCS : C * C + S * S = 1) (x : Joint) :
    jointTurn C S (jointTurn C S x) =
      jointAdd (jointSmul (-1) x) (jointSmul (2 * C) (jointTurn C S x)) := by
  have e : jointTurn C S (jointTurn C S x) =
      jointAdd (jointSmul (-(C * C + S * S)) x) (jointSmul (2 * C) (jointTurn C S x)) := by
    apply Joint.ext <;> dsimp only [jointTurn, jointAdd, jointSmul] <;> ring
  rw [hCS] at e
  exact e

theorem jointAdd_zero_left (x : Joint) : jointAdd jointZero x = x := by
  apply Joint.ext <;> dsimp only [jointAdd, jointZero] <;> ring

theorem jointAdd_zero_right (x : Joint) : jointAdd x jointZero = x := by
  apply Joint.ext <;> dsimp only [jointAdd, jointZero] <;> ring

theorem all_on_one_sheet (C S : ℝ) (hCS : C * C + S * S = 1) (hS : S ≠ 0) (Held : Set Sheets)
    (hadd : ∀ p ∈ Held, ∀ q ∈ Held, sheetsAdd p q ∈ Held)
    (hfo : ∀ p ∈ Held, ∃ α β : ℝ, coTurn C S (coTurn C S p) =
      sheetsAdd (sheetsSmul α p) (sheetsSmul β (coTurn C S p))) :
    (∀ p ∈ Held, p.anti = jointZero) ∨ (∀ p ∈ Held, p.sync = jointZero) := by
  by_cases h1 : ∀ p ∈ Held, p.anti = jointZero
  · exact Or.inl h1
  right
  intro q hq
  obtain ⟨p, hp⟩ := not_forall.mp h1
  obtain ⟨hpH, hpa⟩ := Classical.not_imp.mp hp
  have hps : p.sync = jointZero :=
    (one_sheet_of_firstOrder C S hCS hS p (hfo p hpH)).resolve_right hpa
  rcases one_sheet_of_firstOrder C S hCS hS (sheetsAdd p q) (hfo _ (hadd p hpH q hq)) with h | h
  · dsimp only [sheetsAdd] at h
    rw [hps, jointAdd_zero_left] at h
    exact h
  · rcases one_sheet_of_firstOrder C S hCS hS q (hfo q hq) with hq0 | hq0
    · exact hq0
    · exfalso
      dsimp only [sheetsAdd] at h
      rw [hq0, jointAdd_zero_right] at h
      exact hpa h

end APFPaper5.K4


theorem solution :
∀ (C S : Real)
  (hCS :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C C)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) S S))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hS : @Ne.{1} Real S (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (p : APFPaper5.K4.Sheets)
  (hfo :
    @Exists.{1} Real fun (α : Real) =>
      @Exists.{1} Real fun (β : Real) =>
        @Eq.{1} APFPaper5.K4.Sheets (APFPaper5.K4.coTurn C S (APFPaper5.K4.coTurn C S p))
          (APFPaper5.K4.sheetsAdd (APFPaper5.K4.sheetsSmul α p)
            (APFPaper5.K4.sheetsSmul β (APFPaper5.K4.coTurn C S p)))),
  Or (@Eq.{1} APFPaper5.K4.Joint (APFPaper5.K4.Sheets.sync p) APFPaper5.K4.jointZero)
    (@Eq.{1} APFPaper5.K4.Joint (APFPaper5.K4.Sheets.anti p) APFPaper5.K4.jointZero) := by
  exact @APFPaper5.K4.one_sheet_of_firstOrder
