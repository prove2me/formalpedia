-- Prove2me | solution 1 for AryaANN.Search.rect_diam_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-24T09:46:24.645869+00:00
-- url     : https://prove2.me/submissions/c46d34f8-1934-400a-9a0a-b591188523ab

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search
 theorem rect_coord_bound {d : ℕ} (R : Rect d) (x y : Fin d → ℝ)
    (hx : x ∈ R.toSet) (hy : y ∈ R.toSet) (i : Fin d) :
    |x i - y i| ≤ R.size := by
  have hxi := (Set.mem_Icc.mp hx)
  have hyi := (Set.mem_Icc.mp hy)
  have hcoord : |x i - y i| ≤ R.len i := by
    rw [abs_le]
    constructor <;> dsimp [Rect.len] <;> linarith [hxi.1 i, hxi.2 i, hyi.1 i, hyi.2 i]
  exact hcoord.trans (le_ciSup (Finite.bddAbove_range (fun j : Fin d => R.len j)) i)
 theorem rect_power_sum_bound {d : ℕ} (R : Rect d) (x y : Fin d → ℝ)
    (hx : x ∈ R.toSet) (hy : y ∈ R.toSet) (k : ℕ) :
    ∑ i, |x i - y i| ^ k ≤ (d : ℝ) * R.size ^ k := by
  calc
    _ ≤ ∑ _i : Fin d, R.size ^ k := Finset.sum_le_sum (fun i _ =>
      pow_le_pow_left₀ (abs_nonneg _) (rect_coord_bound R x y hx hy i) k)
    _ = _ := by simp
end AryaANN.Search


open AryaANN.Search

theorem solution {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (R : Rect d) :
    ∀ x ∈ R.toSet, ∀ y ∈ R.toSet,
      lmDist m x y ≤ (d : ℝ) * R.size ∧
      (m ≠ ⊤ → lmDist m x y ≤ (d : ℝ) ^ ((1 : ℝ) / m.toNat) * R.size) := by
  intro x hx y hy
  have hk (hmt : m ≠ ⊤) : 1 ≤ m.toNat := by
    simpa using ENat.toNat_le_toNat hm hmt
  by_cases hd : d = 0
  · subst d
    by_cases hmt : m = ⊤
    · simp [lmDist, hmt]
    · have hkp : (0 : ℝ) < (m.toNat : ℝ) := by exact_mod_cast hk hmt
      have hr : (m.toNat : ℝ)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hkp)
      simp [lmDist, hmt, Real.zero_rpow hr]
  · have hdp : 0 < d := Nat.pos_of_ne_zero hd
    have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdp
    have hsize : 0 ≤ R.size :=
      (abs_nonneg (x ⟨0, hdp⟩ - y ⟨0, hdp⟩)).trans
        (rect_coord_bound R x y hx hy ⟨0, hdp⟩)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdp
    by_cases hmt : m = ⊤
    · constructor
      · calc
          lmDist m x y = ⨆ i, |x i - y i| := by simp [lmDist, hmt]
          _ ≤ R.size := ciSup_le (rect_coord_bound R x y hx hy)
          _ ≤ (d : ℝ) * R.size := by nlinarith
      · exact fun h => (h hmt).elim
    · have hk1 : (1 : ℝ) ≤ m.toNat := by exact_mod_cast hk hmt
      have hkp : (0 : ℝ) < m.toNat := by linarith
      have hsharp : lmDist m x y ≤ (d : ℝ) ^ ((1 : ℝ) / m.toNat) * R.size := by
        calc
          lmDist m x y = (∑ i, |x i - y i| ^ m.toNat) ^ ((1 : ℝ) / m.toNat) := by
            simp [lmDist, hmt]
          _ ≤ ((d : ℝ) * R.size ^ m.toNat) ^ ((1 : ℝ) / m.toNat) :=
            Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _))
              (rect_power_sum_bound R x y hx hy m.toNat) (by positivity)
          _ = (d : ℝ) ^ ((1 : ℝ) / m.toNat) * R.size := by
            rw [Real.mul_rpow (Nat.cast_nonneg d) (pow_nonneg hsize _)]
            rw [one_div, Real.pow_rpow_inv_natCast hsize (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hk hmt)))]
      constructor
      · calc
          lmDist m x y ≤ (d : ℝ) ^ ((1 : ℝ) / m.toNat) * R.size := hsharp
          _ ≤ (d : ℝ) * R.size := mul_le_mul_of_nonneg_right
            (Real.rpow_le_self_of_one_le hd1 ((div_le_one hkp).mpr hk1)) hsize
      · exact fun _ => hsharp


#print axioms solution
