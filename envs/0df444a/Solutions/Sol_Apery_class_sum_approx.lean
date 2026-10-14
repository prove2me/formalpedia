-- Prove2me | solution 1 for Apery.class_sum_approx
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:25:52.341996+00:00
-- url     : https://prove2.me/submissions/ba4efaa7-9f19-4c7a-8f15-16f6afd4483b

/-
# Class sums versus their continuous limit (source `Apery/Growth/ClassSum.lean`)

Proves the platform theorem `Apery.class_sum_approx`: the per-class sum
`∑_{c ≤ m} h(a_c, a'_c)` differs from its continuous limit `p ∑_{i,j} b_{ij} c_{ij}(v/p, v'/p)`
by at most `5/2 ∑|b_{ij}|`. Port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
/-!
# Class sums versus their continuous limit (source `Apery/Growth/ClassSum.lean`)

This file proves the platform theorem `Apery.class_sum_approx`: the per-class sum
`∑_{c ≤ m} h(a_c, a'_c)` differs from its continuous limit
`p ∑_{i,j} b_{ij} c_{ij}(v/p, v'/p)` by at most `5/2 ∑|b_{ij}|`, with `a_c` the class counts.
A faithful port of mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/ClassSum.lean`.
-/

set_option autoImplicit false

open Finset

namespace Apery

/-!
# Class sums and their continuous limits

For `p = 2m + 1` and `0 ≤ v, v' < p` put, for `1 ≤ c ≤ m`,
`a_c = [c ≤ v] + [p - v ≤ c]` and `a'_c = [c ≤ v'] + [p - v' ≤ c]`.
Every function `h` of `(a_c, a'_c)` is a combination of the products of the interval indicators
`1 = [1 ≤ c ≤ m]`, `A = [c ≤ v]`, `E = [p - v ≤ c]`, so `∑_c h(a_c, a'_c)` is a combination of
nine interval counts. Each count is within `5/2` of `p` times its continuous analogue, where
`v/p = f`, `v'/p = g`.

We also prove `SX p X c = 2 ⌊X/p⌋ + a_c(X mod p)`.
-/

open Finset


lemma expand_one {p m v c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hc1 : 1 ≤ c) (hcm : c ≤ m)
    (h : ℕ → ℝ) : h (aCnt p v c) = ∑ i, bcoef h i * ivInd p m v i c := by
  simp only [Fin.sum_univ_three, bcoef, ivInd, ivLo, ivHi, aCnt, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  by_cases h1 : c ≤ v <;> by_cases h2 : p - v ≤ c
  · simp [h1, h2, hc1, hcm]
  · simp [h1, h2, hc1, hcm]
  · exfalso; omega
  · simp [h1, h2, hc1, hcm]

lemma expand_two {p m v v' c : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (hc1 : 1 ≤ c)
    (hcm : c ≤ m) (h : ℕ → ℕ → ℝ) :
    h (aCnt p v c) (aCnt p v' c) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i * (ivInd p m v i c * ivInd p m v' j c) := by
  rw [expand_one hm hv hc1 hcm (fun a => h a (aCnt p v' c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ a, h a (aCnt p v' c) = ∑ j, bcoef (fun b => h a b) j * ivInd p m v' j c :=
    fun a => expand_one hm hv' hc1 hcm (fun b => h a b)
  simp only [e]
  simp only [bcoef, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fin_cases i <;> simp <;> ring

/-- The discrete count of an intersection of two intervals within `[1, m]`. -/
lemma card_two_intervals (m lo hi lo' hi' : ℕ) :
    ((Icc 1 m).filter fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')).card =
      min (min hi hi') m + 1 - max (max lo lo') 1 := by
  have : (Icc 1 m).filter (fun c => (lo ≤ c ∧ c ≤ hi) ∧ (lo' ≤ c ∧ c ≤ hi')) =
      Icc (max (max lo lo') 1) (min (min hi hi') m) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]

/-- **Class sums as interval counts.** -/
theorem class_sum {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    ∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) =
      ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        ((min (min (ivHi m v i) (ivHi m v' j)) m + 1 - max (max (ivLo p v i) (ivLo p v' j)) 1 : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl fun c hc => expand_two hm hv hv' (Finset.mem_Icc.mp hc).1
    (Finset.mem_Icc.mp hc).2 h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← card_two_intervals]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [ivInd]
  split_ifs <;> simp_all

lemma cast_trunc_sub (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  rcases le_or_gt b a with h | h
  · have h' : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.cast_sub h, max_eq_right (by linarith)]
  · have h' : (a : ℝ) < b := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h.le, max_eq_left (by linarith)]
    simp

lemma abs_max0_sub (u w : ℝ) : |max 0 u - max 0 w| ≤ |u - w| := by
  have := abs_max_sub_max_le_max (0 : ℝ) u 0 w
  simpa using this

lemma hi_approx {p m v : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (i : Fin 3) :
    |(ivHi m v i : ℝ) - p * cvHi ((v : ℝ) / p) i| ≤ 1 / 2 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  fin_cases i <;> simp [ivHi, cvHi, hmR]
  · rw [abs_le]; constructor <;> linarith
  · rw [mul_div_cancel₀ _ hp.ne']; simp
  · rw [abs_le]; constructor <;> linarith

lemma lo_approx {p v : ℕ} (hv : v < p) (i : Fin 3) :
    |(ivLo p v i : ℝ) - p * cvLo ((v : ℝ) / p) i| ≤ 1 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  fin_cases i <;> simp [ivLo, cvLo]
  rw [Nat.cast_sub hv.le, mul_sub, mul_one, mul_div_cancel₀ _ hp.ne']
  simp

/-- **Each interval count is within `5/2` of `p` times its continuous analogue.** -/
lemma count_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p) (i j : Fin 3) :
    |((min (min (ivHi m v i) (ivHi m v' j)) m + 1 - max (max (ivLo p v i) (ivLo p v' j)) 1 : ℕ) : ℝ) -
      (p : ℝ) * ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤ 5 / 2 := by
  have hp : (0 : ℝ) < p := by have : 0 < p := by omega
                              exact_mod_cast this
  have hmR : (m : ℝ) = (p - 1) / 2 := by
    have : ((2 * m + 1 : ℕ) : ℝ) = p := by exact_mod_cast hm
    push_cast at this; linarith
  rw [cast_trunc_sub]
  unfold ccount
  rw [mul_max_of_nonneg _ _ hp.le, mul_zero, mul_sub, mul_min_of_nonneg _ _ hp.le,
    mul_min_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le, mul_max_of_nonneg _ _ hp.le, mul_zero]
  refine (abs_max0_sub _ _).trans ?_
  push_cast
  have h1 : |min (min (ivHi m v i : ℝ) (ivHi m v' j)) m -
      min (min (p * cvHi ((v : ℝ) / p) i) (p * cvHi ((v' : ℝ) / p) j)) (p * (1 / 2))| ≤ 1 / 2 := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
    · exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hi_approx hm hv i) (hi_approx hm hv' j))
    · rw [hmR, abs_le]; constructor <;> linarith
  have h2 : |max (max (ivLo p v i : ℝ) (ivLo p v' j)) 1 -
      max (max (p * cvLo ((v : ℝ) / p) i) (p * cvLo ((v' : ℝ) / p) j)) 0| ≤ 1 := by
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ (by norm_num))
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (lo_approx hv i) (lo_approx hv' j))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Class sums versus their continuous limit.** -/
theorem class_sum_approx {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (aCnt p v c) (aCnt p v' c) -
      (p : ℝ) * ∑ i, ∑ j, bcoef (fun a => bcoef (fun b => h a b) j) i *
        ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 * ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| := by
  rw [class_sum hm hv hv', Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm, ← mul_sub, abs_mul, mul_comm (5 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (count_approx hm hv hv' i j) (abs_nonneg _)

end Apery

#check @Apery.class_sum_approx
end Port0


open Finset in
/-- The platform target `Apery.class_sum_approx`, restated at top level as `solution`. -/
theorem solution {p m v v' : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (hv' : v' < p)
    (h : ℕ → ℕ → ℝ) :
    |∑ c ∈ Icc 1 m, h (Apery.aCnt p v c) (Apery.aCnt p v' c) -
      (p : ℝ) * ∑ i, ∑ j, Apery.bcoef (fun a => Apery.bcoef (fun b => h a b) j) i *
        Apery.ccount ((v : ℝ) / p) ((v' : ℝ) / p) i j| ≤
      5 / 2 * ∑ i, ∑ j, |Apery.bcoef (fun a => Apery.bcoef (fun b => h a b) j) i| :=
  Apery.class_sum_approx hm hv hv' h
