-- Prove2me | solution 1 for AaronsonAmbainis.influence_of_meanIncrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:34.808731+00:00
-- url     : https://prove2.me/submissions/29ddeb7b-097d-43a4-a0ac-b7af57ab1247

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Theorems.Thm_AaronsonAmbainis_Average_exists_meanAbsIncr_pos
import Theorems.Thm_AaronsonAmbainis_Average_sum_meanAbsIncr_pos
import Theorems.Thm_AaronsonAmbainis_Average_exists_avg_set
import Theorems.Thm_AaronsonAmbainis_Level_meanAbsIncr_nonneg


set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : MeanIncrementBound → InfluenceBound := by
  intro hMI ι _ _ f K a ha hsum hrow hvar
  classical
  -- the sum `L` of the mean absolute increments is positive
  have hLpos : 0 < ∑ k, meanAbsIncr f k :=
    Average.sum_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = variance f := ⟨_, rfl⟩
  obtain ⟨L, hLf⟩ : ∃ L : ℝ, L = ∑ k, meanAbsIncr f k := ⟨_, rfl⟩
  rw [← hV] at hvar
  rw [← hLf] at hLpos
  rw [← hV, ← hLf]
  -- the average over the coordinates of small influence
  obtain ⟨g, b, hb0, hbK, hbrow, hvarg, -, hL1, hzero⟩ := Average.exists_avg_set f a ha hsum hrow
    (univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j))
  rw [← hV] at hvarg
  have h5 : 5 * L * ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
      inflR f j ≤ 2 * V * L := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          5 * L * inflR f j
        ≤ ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2.le)
      _ ≤ ∑ j, 2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => mul_nonneg (mul_nonneg (by norm_num) hvar.le)
              (Level.meanAbsIncr_nonneg f j))
      _ = 2 * V * L := by rw [← Finset.mul_sum, hLf]
  have hsumR : 5 * ∑ j ∈ univ.filter
      (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j ≤ 2 * V := by
    have h6 : L * (5 * ∑ j ∈ univ.filter
        (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j)
        ≤ L * (2 * V) := by linarith
    exact le_of_mul_le_mul_left h6 hLpos
  have hVg : 3 / 5 * V ≤ variance g := by linarith
  -- the bound for the mean absolute increments of the average
  obtain ⟨j, hgj, hj⟩ :=
    Average.exists_meanAbsIncr_pos hMI g b hb0 hbK hbrow (by linarith : 0 < variance g)
  refine ⟨j, ?_⟩
  have hjR : j ∉ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j) := by
    intro h
    rw [hzero j h] at hgj
    exact lt_irrefl 0 hgj
  have h4 : 2 * V * meanAbsIncr f j ≤ 5 * L * inflR f j := by
    by_contra h
    exact hjR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp h⟩)
  have h2V : (0 : ℝ) ≤ 2 * V := by linarith
  have h7 : 2 * V * meanAbsIncr g j ≤ 5 * L * inflR f j :=
    le_trans (mul_le_mul_of_nonneg_left (hL1 j) h2V) h4
  have h8 : (2 * V * meanAbsIncr g j) ^ 2 ≤ (5 * L * inflR f j) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h2V hgj.le) h7 2
  have h9 : (3 / 5 * V) ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 :=
    le_trans (pow_le_pow_left₀ (by linarith) hVg 3) hj
  have hK4 : (0 : ℝ) ≤ 36 * K ^ 4 := by positivity
  calc 3 * V ^ 5 = 125 / 36 * ((3 / 5 * V) ^ 3 * (2 * V) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * meanAbsIncr g j ^ 2 * (2 * V) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h9 (sq_nonneg _)) (by norm_num)
    _ = 125 / 36 * (36 * K ^ 4 * (2 * V * meanAbsIncr g j) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * (5 * L * inflR f j) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 hK4) (by norm_num)
    _ = 3125 * L ^ 2 * K ^ 4 * inflR f j ^ 2 := by ring
end AaronsonAmbainis
