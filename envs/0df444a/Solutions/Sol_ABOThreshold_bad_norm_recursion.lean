-- Prove2me | solution 1 for ABOThreshold.bad_norm_recursion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:33:55.294417+00:00
-- url     : https://prove2.me/submissions/66424455-2b24-4e62-91eb-cc077d041957

import Definitions.Def_ABOThreshold_model

open ABOThreshold Finset

namespace Ag2Aux_ABOBadNorm

theorem gen (x D δ : ℝ) (k : ℕ) (hx0 : 0 < x) (hx1 : x ≤ 1) (hδk : δ ≤ k) (hD : 0 ≤ D)
    (hthr : D * x ^ (k + 1) < x ^ (1 + δ)) (s : ℝ) (hs : 1 ≤ s) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ x ^ s) : D * c ^ (k + 1) ≤ x ^ (s * (1 + δ)) := by
  have h1 : c ^ (k + 1) ≤ (x ^ s) ^ (k + 1) := pow_le_pow_left₀ hc0 hc _
  have h2 : (x ^ s) ^ (k + 1) = x ^ ((k + 1 : ℕ) : ℝ) * x ^ ((s - 1) * ((k : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1; push_cast; ring
  rw [Real.rpow_natCast] at h2
  have hpos : 0 < x ^ ((s - 1) * ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hx0 _
  calc D * c ^ (k + 1) ≤ D * (x ^ s) ^ (k + 1) := mul_le_mul_of_nonneg_left h1 hD
    _ = (D * x ^ (k + 1)) * x ^ ((s - 1) * ((k : ℝ) + 1)) := by rw [h2]; ring
    _ ≤ x ^ (1 + δ) * x ^ ((s - 1) * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hthr.le hpos.le
    _ = x ^ (1 + δ + (s - 1) * ((k : ℝ) + 1)) := (Real.rpow_add hx0 _ _).symm
    _ ≤ x ^ (s * (1 + δ)) := by
        apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1
        nlinarith

end Ag2Aux_ABOBadNorm

open Ag2Aux_ABOBadNorm

theorem solution (A k : ℕ) (hA : k + 1 ≤ A) (η δ : ℝ) (hη : 0 < η)
    (hηA : 2 * η * (A : ℝ) ≤ 1) (hδ : 0 < δ)
    (hthr : Real.exp 1 * (A.choose (k + 1) : ℝ) * (2 * η) ^ (k + 1) < (2 * η) ^ (1 + δ))
    (b : ℕ → ℝ) (hb0 : ∀ r, 0 ≤ b r) (hbase : b 0 ≤ 2 * η)
    (hstep : ∀ r, b (r + 1) ≤
      (A.choose (k + 1) : ℝ) * b r ^ (k + 1) * (1 + b r) ^ (A - k - 1)) :
    ∀ r : ℕ, b r ≤ (2 * η) ^ ((1 + δ) ^ r) := by
  set x := 2 * η with hx
  have hx0 : 0 < x := by positivity
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hx1 : x ≤ 1 := by nlinarith
  set C : ℝ := (A.choose (k + 1) : ℝ) with hC
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hC]; exact_mod_cast Nat.choose_pos hA
  have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hD1 : 1 ≤ Real.exp 1 * C := by nlinarith
  have hδk : δ ≤ k := by
    by_contra hcon
    push_neg at hcon
    have h1 : x ^ (1 + δ) ≤ x ^ ((k : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at h1
    have hxp : 0 < x ^ (k + 1) := by positivity
    nlinarith
  intro r
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
    set s : ℝ := (1 + δ) ^ r with hs
    have hs1 : 1 ≤ s := one_le_pow₀ (by linarith)
    have hbx : b r ≤ x := by
      calc b r ≤ x ^ s := ih
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hs1
        _ = x := Real.rpow_one x
    have hfac : (1 + b r) ^ (A - k - 1) ≤ Real.exp 1 := by
      have hm : ((A - k - 1 : ℕ) : ℝ) ≤ A := by exact_mod_cast (by omega : A - k - 1 ≤ A)
      calc (1 + b r) ^ (A - k - 1) ≤ (Real.exp (b r)) ^ (A - k - 1) :=
            pow_le_pow_left₀ (by linarith [hb0 r]) (by rw [add_comm]; exact Real.add_one_le_exp _) _
        _ = Real.exp ((A - k - 1 : ℕ) * b r) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp 1 := by
            apply Real.exp_le_exp.mpr
            have := hb0 r
            nlinarith
    have hg := gen x (Real.exp 1 * C) δ k hx0 hx1 hδk (by positivity) hthr s hs1 (b r) (hb0 r) ih
    have hbp : 0 ≤ C * b r ^ (k + 1) := by have := hb0 r; positivity
    calc b (r + 1) ≤ C * b r ^ (k + 1) * (1 + b r) ^ (A - k - 1) := hstep r
      _ ≤ C * b r ^ (k + 1) * Real.exp 1 := mul_le_mul_of_nonneg_left hfac hbp
      _ = Real.exp 1 * C * b r ^ (k + 1) := by ring
      _ ≤ x ^ (s * (1 + δ)) := hg
      _ = x ^ ((1 + δ) ^ (r + 1)) := by rw [hs, pow_succ]
