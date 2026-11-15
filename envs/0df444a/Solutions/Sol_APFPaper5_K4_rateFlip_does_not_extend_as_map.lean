-- Prove2me | solution 1 for APFPaper5.K4.rateFlip_does_not_extend_as_map
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T08:06:07.693595+00:00
-- url     : https://prove2.me/submissions/42cbcfba-e1a8-4c51-9e2a-0a6a80d49135

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_record_book_linear
title: After an additive homogeneous map of joint states that leaves the quarter turn unseen, a cost is linear in the joint record book; so the rate flip of one part extends to no such map
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_JointCarrier. Author's ruling of 2026-11-13: route C.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model of composition.
statement: (joint_expand) an additive homogeneous map of joint states is fixed by its values on the eight
 unit joint states.
 (recDiag_jointQuarter) the cost recDiag is unchanged by the quarter turn of the joint state.
 (linear_of_additive_quarter_unseen) if a map of joint states is additive and homogeneous, and the quarter
 turn of the joint state is unseen by the cost recDiag after it, that cost after the map is linear in the
 joint record book.
 (extendsToJoint_of_map) so extension as such a map gives extension in the sense of
 Def_APFPaper5_K4_JointCarrier.
 (rateFlip_does_not_extend_as_map) the rate flip of the first part extends to no such map.
reading: "linear in the joint record book" is not a premise of its own. It follows from the two clauses
 already used on one system: maps are additive and homogeneous, and the common turn stays unseen.
not_claimed: that admitted maps of joint states at an interface are additive and homogeneous and leave the
 common turn unseen; the composition clause; any K.
-/
import Definitions.Def_APFPaper5_K4_JointCarrier
import Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
import Theorems.Thm_APFPaper5_K4_flipped_part_record_value
import Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
import Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace APFPaper5.K4

open APFPaper5.K3

theorem joint_expand (F : Joint → Joint) (hlin : JointAdditiveHomogeneous F) (p : Joint) :
    F p =
      jointAdd (jointAdd (jointAdd (jointSmul p.x1 (F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩)) (jointSmul p.y1 (F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩))) (jointAdd (jointSmul p.x2 (F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩)) (jointSmul p.y2 (F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩))))
        (jointAdd (jointAdd (jointSmul p.x3 (F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩)) (jointSmul p.y3 (F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩))) (jointAdd (jointSmul p.x4 (F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩)) (jointSmul p.y4 (F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩)))) := by
  have hh : p =
      jointAdd (jointAdd (jointAdd (jointSmul p.x1 ⟨1, 0, 0, 0, 0, 0, 0, 0⟩) (jointSmul p.y1 ⟨0, 1, 0, 0, 0, 0, 0, 0⟩)) (jointAdd (jointSmul p.x2 ⟨0, 0, 1, 0, 0, 0, 0, 0⟩) (jointSmul p.y2 ⟨0, 0, 0, 1, 0, 0, 0, 0⟩)))
        (jointAdd (jointAdd (jointSmul p.x3 ⟨0, 0, 0, 0, 1, 0, 0, 0⟩) (jointSmul p.y3 ⟨0, 0, 0, 0, 0, 1, 0, 0⟩)) (jointAdd (jointSmul p.x4 ⟨0, 0, 0, 0, 0, 0, 1, 0⟩) (jointSmul p.y4 ⟨0, 0, 0, 0, 0, 0, 0, 1⟩))) := by
    apply Joint.ext <;> dsimp only [jointAdd, jointSmul] <;> ring
  have e := congrArg F hh
  rw [hlin.1, hlin.1, hlin.1, hlin.1, hlin.1, hlin.1, hlin.1, hlin.2, hlin.2, hlin.2, hlin.2, hlin.2,
    hlin.2, hlin.2, hlin.2] at e
  exact e

theorem recDiag_jointQuarter (p : Joint) : recDiag (jointQuarter p) = recDiag p := by
  dsimp only [recDiag, jointQuarter]
  ring

theorem linear_of_additive_quarter_unseen (F : Joint → Joint) (hlin : JointAdditiveHomogeneous F)
    (hq : ∀ p : Joint, recDiag (F (jointQuarter p)) = recDiag (F p)) :
    ∃ w : RecordWeights, ∀ p : Joint, recDiag (F p) = linearRecord w p := by
  have hexp := joint_expand F hlin
  generalize F ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = g1 at hexp
  generalize F ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = g2 at hexp
  generalize F ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = g3 at hexp
  generalize F ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = g4 at hexp
  generalize F ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = g5 at hexp
  generalize F ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = g6 at hexp
  generalize F ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = g7 at hexp
  generalize F ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = g8 at hexp
  obtain ⟨A1, hA1⟩ : ∃ A : ℝ, A = g1.x1 + g1.x4 := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : ℝ, A = g2.x1 + g2.x4 := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A : ℝ, A = g3.x1 + g3.x4 := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A : ℝ, A = g4.x1 + g4.x4 := ⟨_, rfl⟩
  obtain ⟨A5, hA5⟩ : ∃ A : ℝ, A = g5.x1 + g5.x4 := ⟨_, rfl⟩
  obtain ⟨A6, hA6⟩ : ∃ A : ℝ, A = g6.x1 + g6.x4 := ⟨_, rfl⟩
  obtain ⟨A7, hA7⟩ : ∃ A : ℝ, A = g7.x1 + g7.x4 := ⟨_, rfl⟩
  obtain ⟨A8, hA8⟩ : ∃ A : ℝ, A = g8.x1 + g8.x4 := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ B : ℝ, B = g1.y1 + g1.y4 := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ B : ℝ, B = g2.y1 + g2.y4 := ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ B : ℝ, B = g3.y1 + g3.y4 := ⟨_, rfl⟩
  obtain ⟨B4, hB4⟩ : ∃ B : ℝ, B = g4.y1 + g4.y4 := ⟨_, rfl⟩
  obtain ⟨B5, hB5⟩ : ∃ B : ℝ, B = g5.y1 + g5.y4 := ⟨_, rfl⟩
  obtain ⟨B6, hB6⟩ : ∃ B : ℝ, B = g6.y1 + g6.y4 := ⟨_, rfl⟩
  obtain ⟨B7, hB7⟩ : ∃ B : ℝ, B = g7.y1 + g7.y4 := ⟨_, rfl⟩
  obtain ⟨B8, hB8⟩ : ∃ B : ℝ, B = g8.y1 + g8.y4 := ⟨_, rfl⟩
  refine ⟨⟨(A1 * A1 + A2 * A2 + B1 * B1 + B2 * B2) / 2,
      (A3 * A3 + A4 * A4 + B3 * B3 + B4 * B4) / 2,
      (A5 * A5 + A6 * A6 + B5 * B5 + B6 * B6) / 2,
      (A7 * A7 + A8 * A8 + B7 * B7 + B8 * B8) / 2,
      A1 * A3 + A2 * A4 + B1 * B3 + B2 * B4,
      -((A1 * A4 - A2 * A3) + (B1 * B4 - B2 * B3)),
      A1 * A5 + A2 * A6 + B1 * B5 + B2 * B6,
      -((A1 * A6 - A2 * A5) + (B1 * B6 - B2 * B5)),
      A1 * A7 + A2 * A8 + B1 * B7 + B2 * B8,
      -((A1 * A8 - A2 * A7) + (B1 * B8 - B2 * B7)),
      A3 * A5 + A4 * A6 + B3 * B5 + B4 * B6,
      -((A3 * A6 - A4 * A5) + (B3 * B6 - B4 * B5)),
      A3 * A7 + A4 * A8 + B3 * B7 + B4 * B8,
      -((A3 * A8 - A4 * A7) + (B3 * B8 - B4 * B7)),
      A5 * A7 + A6 * A8 + B5 * B7 + B6 * B8,
      -((A5 * A8 - A6 * A7) + (B5 * B8 - B6 * B7))⟩, fun p => ?_⟩
  have k := hq p
  rw [hexp p, hexp (jointQuarter p)] at k
  rw [hexp p]
  subst hA1 hA2 hA3 hA4 hA5 hA6 hA7 hA8 hB1 hB2 hB3 hB4 hB5 hB6 hB7 hB8
  dsimp only [recDiag, linearRecord, jointAdd, jointSmul, jointQuarter] at k ⊢
  linear_combination (-1 / 2) * k

theorem extendsToJoint_of_map (T : Held2 → Held2) (hT : ExtendsToJointMap T) : ExtendsToJoint T := by
  obtain ⟨F, hlin, hq, hprod⟩ := hT
  obtain ⟨w, hw⟩ := linear_of_additive_quarter_unseen F hlin hq
  exact ⟨F, w, hw, hprod⟩

theorem rateFlip_does_not_extend_as_map : ¬ ExtendsToJointMap rateFlip :=
  fun hT => rateFlip_does_not_extend (extendsToJoint_of_map rateFlip hT)

end APFPaper5.K4


theorem solution :
Not (APFPaper5.K4.ExtendsToJointMap APFPaper5.K3.rateFlip) := by
  exact @APFPaper5.K4.rateFlip_does_not_extend_as_map
