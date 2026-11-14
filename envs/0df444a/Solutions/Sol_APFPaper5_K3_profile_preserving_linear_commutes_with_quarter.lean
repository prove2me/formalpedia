-- Prove2me | solution 1 for APFPaper5.K3.profile_preserving_linear_commutes_with_quarter
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:34:35.695397+00:00
-- url     : https://prove2.me/submissions/47d21798-d5a8-4b22-81bc-ce33f44b0071

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_direction_is_recorded
title: The quarter-turned recombination record is the plain recombination record read after a quarter turn of one component, so the direction of turning is in the continuation profile
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_ContinuationProfile. The test announced in NOTE_derivation_pass_8_2026-11-13.
consumes_inputs: B01 in the last theorem, in the sense that the conclusion is one of its descent statements.
 The rest consume none. CONDITIONAL INSTANCE in a supplied model.
statement: (recQuarter_eq_recSum_after_quarter_turn) the quarter-turned recombination record of h is the plain
 recombination record of h after component B is turned a quarter.
 (recSum_after_relative_turn) after a turn of B by (c, s) the plain recombination record is the cost of A,
 plus (c * c + s * s) times the cost of B, plus twice (c times the first cross term plus s times the second).
 (number_change_under_relative_turn) so the second cross term is what a turn of one component adds to the
 first, per unit of s. (cross_norm) the squares of the two cross terms add to the product of the two costs.
 (relative_commutes_common) a turn of B commutes with a common turn.
 (plainAfterTurn_commonTurn) a common turn by a unit pair leaves the continuation profile unchanged.
 (plainAfterTurn_determines_quarter) the continuation profile fixes the quarter-turned recombination record.
 (plainAfterTurn_sees_rateFlip) the rate flip changes the continuation profile at one state.
 (plainAfterTurn_determines_plain) the continuation profile fixes the three plain records.
 (profile_preserving_linear_commutes_with_quarter) every additive homogeneous map that leaves the continuation
 profile unchanged commutes with the common quarter turn.
 (APFB01.quarter_record_descends) the value of the quarter-turned recombination record descends to the
 quotient by continuation profile: it is a physical fact in the sense of B01.
reading: no extra record has to be assumed. If a turn of one component is an admissible continuation and the
 plain recombination is a record, the direction of turning is already a physical fact.
not_claimed: that a turn of one component alone is admissible at an interface; that the plain recombination is
 a record there; generator completeness; any K.
-/
import Definitions.Def_APFPaper5_K3_ContinuationProfile
import Definitions.Def_APF_B01_DeclaredInput
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_is_common_turn
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFPaper5_K3_rateFlip_seen_by_quarter_record
import Theorems.Thm_APFPaper5_K3_rateFlip_does_not_commute
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem recQuarter_eq_recSum_after_quarter_turn (h : Held2) :
    recSum (relativeTurn 0 1 h) = recQuarter h := by
  dsimp only [recSum, recQuarter, relativeTurn]
  ring

theorem recSum_after_relative_turn (c s : ℝ) (h : Held2) :
    recSum (relativeTurn c s h) =
      recA h + (c * c + s * s) * recB h + 2 * (c * crossRe h + s * crossIm h) := by
  dsimp only [recSum, recA, recB, crossRe, crossIm, relativeTurn]
  ring

theorem number_change_under_relative_turn (c s : ℝ) (h : Held2) :
    crossRe (relativeTurn c s h) - c * crossRe h = s * crossIm h := by
  dsimp only [crossRe, crossIm, relativeTurn]
  ring

theorem cross_norm (h : Held2) :
    crossRe h * crossRe h + crossIm h * crossIm h = recA h * recB h := by
  dsimp only [crossRe, crossIm, recA, recB]
  ring

theorem relative_commutes_common (c s c' s' : ℝ) (h : Held2) :
    relativeTurn c' s' (commonTurn c s h) = commonTurn c s (relativeTurn c' s' h) := by
  apply Held2.ext <;> dsimp only [relativeTurn, commonTurn] <;> ring

theorem plainAfterTurn_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    plainAfterTurn (commonTurn c s h) = plainAfterTurn h := by
  funext x
  unfold plainAfterTurn
  rw [relative_commutes_common]
  obtain ⟨hA, hB, hS, _⟩ := commonTurn_unseen c s hcs (relativeTurn x.1 x.2.1 h)
  rw [hA, hB, hS]

theorem plainAfterTurn_determines_quarter (h h' : Held2)
    (hprof : plainAfterTurn h = plainAfterTurn h') : recQuarter h = recQuarter h' := by
  have hx : plainAfterTurn h' (0, 1, (recA (relativeTurn 0 1 h), recB (relativeTurn 0 1 h),
      recSum (relativeTurn 0 1 h))) := by
    rw [← hprof]
    exact ⟨by norm_num, rfl⟩
  have h3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) hx.2
  dsimp only at h3
  rw [recQuarter_eq_recSum_after_quarter_turn, recQuarter_eq_recSum_after_quarter_turn] at h3
  exact h3

theorem plainAfterTurn_sees_rateFlip :
    plainAfterTurn (rateFlip ⟨1, 0, 0, 1⟩) ≠ plainAfterTurn ⟨1, 0, 0, 1⟩ := by
  intro hEq
  have h := plainAfterTurn_determines_quarter _ _ hEq
  obtain ⟨h0, h4⟩ := rateFlip_seen_by_quarter_record
  rw [h4, h0] at h
  norm_num at h

theorem relativeTurn_one_zero (h : Held2) : relativeTurn 1 0 h = h := by
  apply Held2.ext <;> dsimp only [relativeTurn] <;> ring

theorem plainAfterTurn_determines_plain (h h' : Held2)
    (hprof : plainAfterTurn h = plainAfterTurn h') :
    recA h = recA h' ∧ recB h = recB h' ∧ recSum h = recSum h' := by
  have hx : plainAfterTurn h' (1, 0, (recA (relativeTurn 1 0 h), recB (relativeTurn 1 0 h),
      recSum (relativeTurn 1 0 h))) := by
    rw [← hprof]
    exact ⟨by norm_num, rfl⟩
  have h1 := congrArg (fun t : ℝ × ℝ × ℝ => t.1) hx.2
  have h2 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) hx.2
  have h3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) hx.2
  dsimp only at h1 h2 h3
  rw [relativeTurn_one_zero, relativeTurn_one_zero] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem profile_preserving_linear_commutes_with_quarter (u1 u2 u3 u4 : Held2)
    (hprof : ∀ h : Held2, plainAfterTurn (combo u1 u2 u3 u4 h) = plainAfterTurn h) (h : Held2) :
    commonTurn 0 1 (combo u1 u2 u3 u4 h) = combo u1 u2 u3 u4 (commonTurn 0 1 h) := by
  apply record_preserving_linear_commutes_with_quarter
  intro k
  obtain ⟨hA, hB, hS⟩ := plainAfterTurn_determines_plain _ _ (hprof k)
  have hQ := plainAfterTurn_determines_quarter _ _ (hprof k)
  obtain ⟨e1, e2⟩ := records_are_cross_data (combo u1 u2 u3 u4 k)
  obtain ⟨f1, f2⟩ := records_are_cross_data k
  refine ⟨hA, hB, ?_, ?_⟩
  · linarith
  · linarith

end APFPaper5.K3

open APFPaper5.K3 in
theorem APFB01.quarter_record_descends (r : ℝ) :
    APFB01.Descends plainAfterTurn (fun h : Held2 => recQuarter h = r) := by
  refine ⟨Quot.lift (fun h : Held2 => recQuarter h = r) (fun h h' hp => ?_), fun h => Iff.rfl⟩
  rw [plainAfterTurn_determines_quarter h h' hp]


theorem solution :
∀ (u1 u2 u3 u4 : APFPaper5.K3.Held2)
  (hprof :
    ∀ (h : APFPaper5.K3.Held2),
      @Eq.{1} ((x : Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real (Prod.{0, 0} Real Real)))) → Prop)
        (APFPaper5.K3.plainAfterTurn (APFPaper5.K3.combo u1 u2 u3 u4 h)) (APFPaper5.K3.plainAfterTurn h))
  (h : APFPaper5.K3.Held2),
  @Eq.{1} APFPaper5.K3.Held2
    (APFPaper5.K3.commonTurn (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (APFPaper5.K3.combo u1 u2 u3 u4 h))
    (APFPaper5.K3.combo u1 u2 u3 u4
      (APFPaper5.K3.commonTurn (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h)) := by
  exact @APFPaper5.K3.profile_preserving_linear_commutes_with_quarter
