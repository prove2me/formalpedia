-- Prove2me | solution 1 for APFPaper5.K1.additive_nonneg_linear
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:25:20.3999+00:00
-- url     : https://prove2.me/submissions/f25a7e69-4aed-4aa4-ac12-d7e82f61bfb4

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_additive_nonneg_linear
title: A nonnegative function that adds over nonnegative reals is a multiple of its argument
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ordinary mathematics (Cauchy's equation with a sign condition). Codebank: L_Cauchy_uniqueness uses the
 same step with monotonicity as the load-bearing clause.
consumes_inputs: none.
statement: (additive_nonneg_linear) if f (s + t) = f s + f t for nonnegative s and t, and f is nonnegative on
 nonnegative reals, then f s = s * f 1 for every nonnegative s.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1

theorem additive_nonneg_linear (f : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → f (s + t) = f s + f t)
    (hnn : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s) :
    ∀ s : ℝ, 0 ≤ s → f s = s * f 1 := by
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → f s ≤ f t := by
    intro s t hs hst
    have h := hadd s (t - s) hs (by linarith)
    have h2 : s + (t - s) = t := by ring
    rw [h2] at h
    have h3 := hnn (t - s) (by linarith)
    linarith
  have hf0 : f 0 = 0 := by
    have h0 := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at h0
    linarith
  have hnat : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → f ((n : ℝ) * s) = (n : ℝ) * f s := by
    intro n s hs
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, hf0]
    | succ k ih =>
      have hk : (0 : ℝ) ≤ (k : ℝ) * s := mul_nonneg (Nat.cast_nonneg k) hs
      have h := hadd ((k : ℝ) * s) s hk hs
      have e : ((k + 1 : ℕ) : ℝ) * s = (k : ℝ) * s + s := by
        rw [Nat.cast_succ]
        ring
      rw [e, h, ih, Nat.cast_succ]
      ring
  intro s hs
  have hc : 0 ≤ f 1 := hnn 1 zero_le_one
  have hbound : ∀ n : ℕ, (n : ℝ) * f s - (n : ℝ) * (s * f 1) ≤ f 1 ∧
      (n : ℝ) * (s * f 1) - (n : ℝ) * f s ≤ f 1 := by
    intro n
    have hns : (0 : ℝ) ≤ (n : ℝ) * s := mul_nonneg (Nat.cast_nonneg n) hs
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) ≤ (n : ℝ) * s ∧ (n : ℝ) * s < (k : ℝ) + 1 :=
      ⟨⌊(n : ℝ) * s⌋₊, Nat.floor_le hns, Nat.lt_floor_add_one _⟩
    have hfk : f (k : ℝ) = (k : ℝ) * f 1 := by
      have h := hnat k 1 zero_le_one
      rwa [mul_one] at h
    have hfk1 : f ((k : ℝ) + 1) = ((k : ℝ) + 1) * f 1 := by
      have h := hnat (k + 1) 1 zero_le_one
      rw [mul_one, Nat.cast_succ] at h
      exact h
    have hlow : f (k : ℝ) ≤ f ((n : ℝ) * s) := hmono _ _ (Nat.cast_nonneg k) hk1
    have hhigh : f ((n : ℝ) * s) ≤ f ((k : ℝ) + 1) := hmono _ _ hns hk2.le
    rw [hnat n s hs] at hlow hhigh
    rw [hfk] at hlow
    rw [hfk1] at hhigh
    have h3 : (k : ℝ) * f 1 ≤ (n : ℝ) * s * f 1 := mul_le_mul_of_nonneg_right hk1 hc
    have h4 : (n : ℝ) * s * f 1 ≤ ((k : ℝ) + 1) * f 1 := mul_le_mul_of_nonneg_right hk2.le hc
    constructor <;> linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hd : 0 < s * f 1 - f s := by linarith
    obtain ⟨n, hn⟩ := Archimedean.arch (f 1 + 1) hd
    rw [nsmul_eq_mul] at hn
    have hb := (hbound n).2
    linarith
  · have hd : 0 < f s - s * f 1 := by linarith
    obtain ⟨n, hn⟩ := Archimedean.arch (f 1 + 1) hd
    rw [nsmul_eq_mul] at hn
    have hb := (hbound n).1
    linarith

end APFPaper5.K1


theorem solution :
∀ (f : Real → Real)
  (hadd :
    ∀ (s t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) s →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
          @Eq.{1} Real (f (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) s t))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f s) (f t)))
  (hnn :
    ∀ (s : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) s →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f s))
  (s : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) s →
    @Eq.{1} Real (f s)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s
        (f (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))) := by
  exact @APFPaper5.K1.additive_nonneg_linear
