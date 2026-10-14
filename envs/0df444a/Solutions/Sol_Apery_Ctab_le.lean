-- Prove2me | solution 1 for Apery.Ctab_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:42:18.016031+00:00
-- url     : https://prove2.me/submissions/2fed52d8-8a31-478e-93b1-1f745e4cc38c

/-
# The additive error of the table bound (source `Apery/Growth/Assembly2.lean`)

Proves the platform theorem `Apery.Ctab_le`. Port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceConstants
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceGrowthErrors

set_option autoImplicit false

section Port0
/-!
# The additive error of the table bound (source `Apery/Growth/Assembly2.lean`)

This file proves the platform theorem `Apery.Ctab_le`: `Ctab n p k ≤ 10^8` whenever
`40n/p ≤ 20` and `k` lies in the admissible window. Port of mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0 (`Apery/Growth/Constants.lean`,
`Apery/Growth/Assembly2.lean`).
-/

set_option autoImplicit false

open Finset

namespace Apery

lemma sum_range_tri (t : ℚ) (L : ℕ) :
    ∑ i ∈ range L, ((t - 2 * i) / 2) = (L : ℚ) * (t - L + 1) / 2 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
lemma psiR_le (k β : ℤ) : psiR k β ≤ ((k - β + 1 : ℤ) : ℚ) ^ 2 / 8 := by
  unfold psiR
  set t := k - β with ht
  have hsum : ∑ i ∈ range (lrow k β), (((k : ℚ) - 2 * i - β) / 2) =
      (lrow k β : ℚ) * ((t : ℚ) - lrow k β + 1) / 2 := by
    rw [← sum_range_tri]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht]; push_cast; ring
  rw [hsum]
  unfold lrow
  rcases le_or_gt (t + 1) 0 with h | h
  · have : ((k - β + 1) / 2).toNat = 0 := by omega
    rw [this]; simp only [Nat.cast_zero, zero_mul, zero_div]; positivity
  · rcases Int.emod_two_eq_zero_or_one t with h2 | h2
    · have e : (((k - β + 1) / 2).toNat : ℚ) = (t : ℚ) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]
    · have e : (((k - β + 1) / 2).toNat : ℚ) = ((t : ℚ) + 1) / 2 := by
        have : (((k - β + 1) / 2).toNat : ℤ) * 2 = t + 1 := by omega
        have : ((((k - β + 1) / 2).toNat : ℤ) : ℚ) * 2 = (t : ℚ) + 1 := by exact_mod_cast this
        push_cast at this; linarith
      rw [e]; push_cast; nlinarith [sq_nonneg ((t : ℚ) + 1)]
lemma lrow_lt {k β : ℤ} {i : ℕ} (hi : i < lrow k β) : 2 * (i : ℚ) + β < k := by
  unfold lrow at hi
  have : 2 * (i : ℤ) + β < k := by omega
  exact_mod_cast this

lemma abs_bcoef_le (h : ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, |h a| ≤ M) (i : Fin 3) : |bcoef h i| ≤ 2 * M := by
  have h0 := hM 0 (by norm_num); have h1 := hM 1 (by norm_num); have h2 := hM 2 (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h0
  fin_cases i <;> simp only [bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linarith
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

lemma abs_bcoef2_le (h : ℕ → ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, ∀ b ≤ 2, |h a b| ≤ M) (i j : Fin 3) :
    |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 4 * M := by
  have := abs_bcoef_le (fun a => bcoef (fun b => h a b) j) (M := 2 * M)
    (fun a ha => abs_bcoef_le (fun b => h a b) (fun b hb => hM a ha b hb) j) i
  linarith

lemma psiR_nonneg (k β : ℤ) : 0 ≤ psiR k β := by
  unfold psiR
  refine Finset.sum_nonneg fun i hi => ?_
  have := lrow_lt (Finset.mem_range.mp hi)
  linarith

lemma abs_psiR_le (k β : ℤ) : |(psiR k β : ℝ)| ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 := by
  have h1 := psiR_nonneg k β
  have h2 := psiR_le k β
  rw [abs_of_nonneg (by exact_mod_cast h1)]
  have : (psiR k β : ℝ) ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 / 8 := by exact_mod_cast h2
  nlinarith [sq_nonneg ((k - β + 1 : ℤ) : ℝ)]

/-- The inner coefficients. -/
lemma sum_abs_bIn_le {q q' : ℕ} (hq' : q' ≤ q) {k : ℤ} (hk1 : -2 * (q : ℤ) - 6 ≤ k)
    (hk2 : k ≤ 8 * (q : ℤ) + 20) :
    ∑ i, ∑ j, |bIn q q' k i j| ≤ 36 * (22 * (q : ℝ) + 30) ^ 2 := by
  have hM : ∀ a : ℕ, a ≤ 2 → ∀ b : ℕ, b ≤ 2 →
      |(psiR k (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) : ℝ)| ≤ (22 * (q : ℝ) + 30) ^ 2 := by
    intro a ha b hb
    refine (abs_psiR_le _ _).trans ?_
    have hb' : (b : ℤ) ≤ 2 := by exact_mod_cast hb
    have ha' : (a : ℤ) ≤ 2 := by exact_mod_cast ha
    have hq'' : (q' : ℤ) ≤ q := by exact_mod_cast hq'
    have hb0 : (0 : ℤ) ≤ b := by positivity
    have ha0 : (0 : ℤ) ≤ a := by positivity
    have hq0 : (0 : ℤ) ≤ q' := by positivity
    have hbd : |k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1| ≤ 22 * (q : ℤ) + 30 := by
      rw [abs_le]; constructor <;> linarith
    have hbdR : |((k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1 : ℤ) : ℝ)| ≤
        22 * (q : ℝ) + 30 := by exact_mod_cast hbd
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbdR 2
  have hb := fun i j => abs_bcoef2_le _ hM i j
  calc ∑ i, ∑ j, |bIn q q' k i j| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (22 * (q : ℝ) + 30) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = 36 * (22 * (q : ℝ) + 30) ^ 2 := by simp; ring

/-- The outer coefficients. -/

lemma Bmax_le {n p Q : ℕ} (hq : 40 * n / p ≤ Q) : Bmax n p ≤ (5 * (Q : ℝ) + 10) * (3 * Q + 6) := by
  unfold Bmax ktopI
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ Q := by exact_mod_cast hq
  have h0' : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := by positivity
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ ⊢
  generalize ((3 * n / p : ℕ) : ℝ) = qR' at h0' ⊢
  set D := max 0 ((8 * qR + 20) / 2 - ((5 + 12 * qR' - 2 * qR) - 4) / 2) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD1 : D ≤ 5 * (Q : ℝ) + 10 := max_le (by positivity) (by linarith)
  nlinarith
lemma ktop_sub_klo (n p : ℕ) : ((ktopI n p - kloI n p : ℤ) : ℝ) = 10 * ((40 * n / p : ℕ) : ℝ) + 26 := by
  unfold ktopI kloI
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_neg]
  ring


lemma Ctab_le {n p : ℕ} (hq : 40 * n / p ≤ 20) {k : ℤ} (hk1 : kloI n p ≤ k) (hk2 : k ≤ ktopI n p) :
    Ctab n p k ≤ 10 ^ 8 := by
  unfold Ctab
  have hq' : 3 * n / p ≤ 40 * n / p := Nat.div_le_div_right (by omega)
  have hk1' : -2 * ((40 * n / p : ℕ) : ℤ) - 6 ≤ k := hk1
  have hk2' : k ≤ 8 * ((40 * n / p : ℕ) : ℤ) + 20 := hk2
  have hs := sum_abs_bIn_le hq' hk1' hk2'
  have hB := Bmax_le (n := n) (p := p) (Q := 20) hq
  rw [ktop_sub_klo]
  unfold L0I
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ 20 := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ ((40 * n / p : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ h0 hs ⊢
  norm_num at hB
  nlinarith

end Apery

#check @Apery.Ctab_le
end Port0


open Finset in
/-- The platform target `Apery.Ctab_le`, restated at top level as `solution`. -/
theorem solution {n p : ℕ} (hq : 40 * n / p ≤ 20) {k : ℤ} (hk1 : Apery.kloI n p ≤ k)
    (hk2 : k ≤ Apery.ktopI n p) : Apery.Ctab n p k ≤ 10 ^ 8 :=
  Apery.Ctab_le hq hk1 hk2
