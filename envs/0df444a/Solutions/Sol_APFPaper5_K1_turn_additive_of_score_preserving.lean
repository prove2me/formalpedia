-- Prove2me | solution 1 for APFPaper5.K1.turn_additive_of_score_preserving
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:57:24.478013+00:00
-- url     : https://prove2.me/submissions/bce8b0bd-2f81-4741-8b91-92eb0dcf5550

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_turn_structure
title: A score-preserving turn that loses nothing acts additively and homogeneously on combinations, and fixes the total of two exclusive marks
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Def_APFPaper5_K1_OrderedScore (IsBilinear); the adopted continuity hypothesis (turns lose nothing);
 PRESERVATION in its score form. Paper 5 Supplement v7.33:427-470.
consumes_inputs: none as a hypothesis. CONDITIONAL on a bilinear score B on a real space of combinations in
 which a combination scoring zero against everything is zero.
statement: (turn_additive_of_score_preserving, turn_homogeneous_of_score_preserving) if T preserves every
 score and every combination is the image of one, then T (a + b) = T a + T b and T (r • a) = r • T a.
 (turn_fixes_total) if also T carries the marks onto the marks, a combination scoring zero against every mark
 is zero, and e scores 1 against every mark, then T e = e.
reading: two hypotheses of Thm_APFPaper5_K1_rank_three (the turn is additive and homogeneous; the turn fixes
 the total) are not extra assumptions. They follow from score preservation, losing nothing, and the clause
 that the total scores 1 against every mark.
not_claimed: the bilinear score itself; that every score is preserved; that the total scores 1 against every
 mark.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem turn_additive_of_score_preserving (B : V → V → ℝ) (hB : IsBilinear B)
    (hnd : ∀ v : V, (∀ c : V, B v c = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hsurj : ∀ c : V, ∃ c' : V, T c' = c) :
    ∀ a b : V, T (a + b) = T a + T b := by
  obtain ⟨h1, h2, _, _⟩ := hB
  intro a b
  have hd : T (a + b) + (-1 : ℝ) • (T a + T b) = 0 := by
    apply hnd
    intro c
    obtain ⟨c', rfl⟩ := hsurj c
    simp only [h1, h2, hiso]
    ring
  rw [neg_one_smul] at hd
  have h := eq_neg_of_add_eq_zero_left hd
  rw [neg_neg] at h
  exact h

theorem turn_homogeneous_of_score_preserving (B : V → V → ℝ) (hB : IsBilinear B)
    (hnd : ∀ v : V, (∀ c : V, B v c = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hsurj : ∀ c : V, ∃ c' : V, T c' = c) :
    ∀ (r : ℝ) (a : V), T (r • a) = r • T a := by
  obtain ⟨h1, h2, _, _⟩ := hB
  intro r a
  have hd : T (r • a) + (-1 : ℝ) • (r • T a) = 0 := by
    apply hnd
    intro c
    obtain ⟨c', rfl⟩ := hsurj c
    simp only [h1, h2, hiso]
    ring
  rw [neg_one_smul] at hd
  have h := eq_neg_of_add_eq_zero_left hd
  rw [neg_neg] at h
  exact h

theorem turn_fixes_total (B : V → V → ℝ) (hB : IsBilinear B) (Marks : Set V)
    (hspan : ∀ v : V, (∀ m ∈ Marks, B v m = 0) → v = 0) (T : V → V)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b)
    (honto : ∀ m ∈ Marks, ∃ n ∈ Marks, T n = m) (e : V)
    (hnorm : ∀ m ∈ Marks, B e m = 1) : T e = e := by
  obtain ⟨h1, h2, _, _⟩ := hB
  have hd : T e + (-1 : ℝ) • e = 0 := by
    apply hspan
    intro m hm
    obtain ⟨n, hn, rfl⟩ := honto m hm
    simp only [h1, h2, hiso]
    rw [hnorm n hn, hnorm (T n) hm]
    ring
  rw [neg_one_smul] at hd
  have h := eq_neg_of_add_eq_zero_left hd
  rw [neg_neg] at h
  exact h

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (B : V → V → Real) (hB : @APFPaper5.K1.IsBilinear.{apfNative_u_1, apfNative_u_1} V V inst inst_1 inst inst_1 B)
  (hnd :
    ∀ (v : V),
      (∀ (c : V), @Eq.{1} Real (B v c) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
        @Eq.{apfNative_u_1 + 1} V v
          (@OfNat.ofNat.{apfNative_u_1} V (nat_lit 0)
            (@Zero.toOfNat0.{apfNative_u_1} V
              (@NegZeroClass.toZero.{apfNative_u_1} V
                (@SubNegZeroMonoid.toNegZeroClass.{apfNative_u_1} V
                  (@SubtractionMonoid.toSubNegZeroMonoid.{apfNative_u_1} V
                    (@SubtractionCommMonoid.toSubtractionMonoid.{apfNative_u_1} V
                      (@AddCommGroup.toDivisionAddCommMonoid.{apfNative_u_1} V inst))))))))
  (T : V → V) (hiso : ∀ (a b : V), @Eq.{1} Real (B (T a) (T b)) (B a b))
  (hsurj : ∀ (c : V), @Exists.{apfNative_u_1 + 1} V fun (c' : V) => @Eq.{apfNative_u_1 + 1} V (T c') c) (a b : V),
  @Eq.{apfNative_u_1 + 1} V
    (T
      (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
        (@instHAdd.{apfNative_u_1} V
          (@AddCommMagma.toAdd.{apfNative_u_1} V
            (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
              (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
        a b))
    (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
      (@instHAdd.{apfNative_u_1} V
        (@AddCommMagma.toAdd.{apfNative_u_1} V
          (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
            (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
              (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
      (T a) (T b)) := by
  exact @APFPaper5.K1.turn_additive_of_score_preserving
