-- Prove2me | solution 1 for APFPaper5.K3.twoMark_continuity_at_every_resolution
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T04:01:35.758796+00:00
-- url     : https://prove2.me/submissions/0bb6acaa-91a4-40c6-89a4-f90f1d211045

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_continuity_at_resolution
title: The re-read continuity clause is weaker than the clause as first typed, and every theorem that used the first form follows from the re-read one at a fine enough resolution
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K3_ContinuityAtResolution (the author's ruling of 2026-11-14 12:47 HST,
 RULING_continuity_reread_2026-11-14) and Def_APFPaper5_K3_Continuity (the first typed form). The three
 theorems of this seat that consumed the first form: exists_value_not_zero_or_one and
 exists_noncommuting_of_rangesOver (Thm_APFPaper5_K3_continuity_consequences), moves_of_continuity
 (Thm_APFB07_moves). Paper 5 Supplement v7.33:3049-3058 (K3). FOUNDATION_INPUTS is not consumed.
consumes_inputs: none.
named_hypotheses: the re-read continuity clause, where a theorem takes it as a hypothesis.
statement: (continuityAtResolution_of_continuity) the first form gives the re-read form at every fineness.
 (continuityAtResolution_mono) a coarser fineness follows from a finer one.
 (exists_value_not_zero_or_one_at_resolution) if the fineness is less than a quarter of the range, some state
 has a relation number that is neither 0 nor 1. (exists_noncommuting_at_resolution) then, for two record
 projections whose pair number is the relation number, some state has them not commuting.
 (moves_at_resolution) if the fineness is less than half the range, from every state some admissible turn
 changes the relation. (twoMark_continuity_at_every_resolution) the two-component model meets the re-read
 clause at every fineness, given square roots.
reading: nothing proved from the first form is lost by the re-reading. The two-component model still meets
 the clause.
not_claimed: that the clause holds; that any turn is admitted.
-/
import Definitions.Def_APFPaper5_K3_ContinuityAtResolution
import Theorems.Thm_APFPaper5_K3_turn_two_sided_inverse_of_loseNothing
import Theorems.Thm_APFPaper5_K3_exists_noncommuting_of_rangesOver
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

universe u uA

theorem rangesAtResolution_of_rangesOver {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ)
    (hd : 0 ≤ delta) (h : RangesOverInterval rel lo hi) : RangesAtResolution rel lo hi delta := by
  refine ⟨h.1, fun t h1 h2 => ?_⟩
  obtain ⟨s, hs⟩ := h.2 t h1 h2
  exact ⟨s, by rw [hs, sub_self, abs_zero]; exact hd⟩

theorem turnsReachAtResolution_of_turnsReach {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ)
    (Adm : Set (S → S)) (hd : 0 ≤ delta) (h : TurnsReach rel lo hi Adm) :
    TurnsReachAtResolution rel lo hi delta Adm := by
  intro s t h1 h2
  obtain ⟨f, hf, hs⟩ := h s t h1 h2
  exact ⟨f, hf, by rw [hs, sub_self, abs_zero]; exact hd⟩

theorem continuityAtResolution_of_continuity {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ)
    (Adm : Set (S → S)) (hd : 0 ≤ delta) (h : Continuity rel lo hi Adm) :
    ContinuityAtResolution rel lo hi delta Adm :=
  ⟨rangesAtResolution_of_rangesOver rel lo hi delta hd h.1,
    turnsReachAtResolution_of_turnsReach rel lo hi delta Adm hd h.2.1, h.2.2⟩

theorem continuityAtResolution_mono {S : Type u} (rel : S → ℝ) (lo hi delta delta' : ℝ)
    (Adm : Set (S → S)) (hle : delta ≤ delta') (h : ContinuityAtResolution rel lo hi delta Adm) :
    ContinuityAtResolution rel lo hi delta' Adm := by
  refine ⟨⟨h.1.1, fun t h1 h2 => ?_⟩, fun s t h1 h2 => ?_, h.2.2⟩
  · obtain ⟨s, hs⟩ := h.1.2 t h1 h2
    exact ⟨s, le_trans hs hle⟩
  · obtain ⟨f, hf, hs⟩ := h.2.1 s t h1 h2
    exact ⟨f, hf, le_trans hs hle⟩

theorem exists_far_from_two (lo hi delta a b : ℝ) (hlt : lo < hi) (h : 4 * delta < hi - lo) :
    ∃ t : ℝ, lo ≤ t ∧ t ≤ hi ∧ delta < |t - a| ∧ delta < |t - b| := by
  by_cases g1 : delta < |lo - a| ∧ delta < |lo - b|
  · exact ⟨lo, le_rfl, hlt.le, g1.1, g1.2⟩
  by_cases g2 : delta < |(lo + hi) / 2 - a| ∧ delta < |(lo + hi) / 2 - b|
  · exact ⟨(lo + hi) / 2, by linarith, by linarith, g2.1, g2.2⟩
  have b1 : |lo - a| ≤ delta ∨ |lo - b| ≤ delta := by
    by_contra hno
    exact g1 ⟨lt_of_not_ge fun h1 => hno (Or.inl h1), lt_of_not_ge fun h1 => hno (Or.inr h1)⟩
  have b2 : |(lo + hi) / 2 - a| ≤ delta ∨ |(lo + hi) / 2 - b| ≤ delta := by
    by_contra hno
    exact g2 ⟨lt_of_not_ge fun h1 => hno (Or.inl h1), lt_of_not_ge fun h1 => hno (Or.inr h1)⟩
  refine ⟨hi, hlt.le, le_rfl, ?_, ?_⟩
  · rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;>
      have q1 := abs_le.mp h1 <;> have q2 := abs_le.mp h2 <;>
      exact lt_abs.mpr (Or.inl (by linarith [q1.1, q1.2, q2.1, q2.2]))
  · rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;>
      have q1 := abs_le.mp h1 <;> have q2 := abs_le.mp h2 <;>
      exact lt_abs.mpr (Or.inl (by linarith [q1.1, q1.2, q2.1, q2.2]))

theorem exists_value_not_zero_or_one_at_resolution {S : Type u} (rel : S → ℝ)
    (lo hi delta : ℝ) (hd : 4 * delta < hi - lo) (h : RangesAtResolution rel lo hi delta) :
    ∃ s : S, rel s ≠ 0 ∧ rel s ≠ 1 := by
  obtain ⟨t, h1, h2, ha, hb⟩ := exists_far_from_two lo hi delta 0 1 h.1 hd
  obtain ⟨s, hs⟩ := h.2 t h1 h2
  refine ⟨s, fun h0 => ?_, fun h0 => ?_⟩
  · rw [h0, zero_sub, abs_neg] at hs
    rw [sub_zero] at ha
    linarith
  · rw [h0, abs_sub_comm] at hs
    linarith

theorem exists_noncommuting_at_resolution {S : Type u} {A : Type uA} [Ring A] [Algebra ℝ A]
    (p q : S → A) (rel : S → ℝ) (lo hi delta : ℝ)
    (hp : ∀ s : S, p s * p s = p s) (hq : ∀ s : S, q s * q s = q s) (hp0 : ∀ s : S, p s ≠ 0)
    (hrel : ∀ s : S, p s * q s * p s = rel s • p s)
    (hd : 4 * delta < hi - lo) (h : RangesAtResolution rel lo hi delta) :
    ∃ s : S, p s * q s ≠ q s * p s := by
  obtain ⟨s, h0, h1⟩ := exists_value_not_zero_or_one_at_resolution rel lo hi delta hd h
  refine ⟨s, fun hcomm => ?_⟩
  rcases APFPaper1.RecordBook.pair_number_zero_or_one_of_commute (p s) (q s) (rel s)
      (hp s) (hq s) hcomm (hrel s) (hp0 s) with hz | ho
  · exact h0 hz
  · exact h1 ho

theorem moves_at_resolution {S : Type u} (rel : S → ℝ) (lo hi delta : ℝ) (Adm : Set (S → S))
    (hd : 2 * delta < hi - lo) (hc : ContinuityAtResolution rel lo hi delta Adm) (s : S) :
    ∃ f ∈ Adm, rel (f s) ≠ rel s := by
  have hlt : lo < hi := hc.1.1
  by_cases g : delta < |lo - rel s|
  · obtain ⟨f, hf, hs⟩ := hc.2.1 s lo le_rfl hlt.le
    refine ⟨f, hf, fun e => ?_⟩
    rw [e, abs_sub_comm] at hs
    linarith
  · have g' : |lo - rel s| ≤ delta := le_of_not_gt g
    obtain ⟨f, hf, hs⟩ := hc.2.1 s hi hlt.le le_rfl
    refine ⟨f, hf, fun e => ?_⟩
    rw [e] at hs
    have q1 := abs_le.mp g'
    have q2 := abs_le.mp hs
    linarith [q1.1, q1.2, q2.1, q2.2]

theorem twoMark_continuity_at_every_resolution (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t)
    (delta : ℝ) (hd : 0 ≤ delta) :
    ContinuityAtResolution relNumber 0 1 delta admTurns :=
  continuityAtResolution_of_continuity relNumber 0 1 delta admTurns hd (twoMark_continuity hroot)

end APFPaper5.K3


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          @Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t)
  (delta : Real)
  (hd : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta),
  @APFPaper5.K3.ContinuityAtResolution.{0} APFPaper5.K3.UnitPair APFPaper5.K3.relNumber
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) delta APFPaper5.K3.admTurns := by
  exact @APFPaper5.K3.twoMark_continuity_at_every_resolution
