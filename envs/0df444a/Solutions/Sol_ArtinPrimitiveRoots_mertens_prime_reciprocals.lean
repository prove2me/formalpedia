-- Prove2me | solution 1 for ArtinPrimitiveRoots.mertens_prime_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T09:30:47.696995+00:00
-- url     : https://prove2.me/submissions/380347dd-eb82-4ebf-be56-9334e9af5334

import Mathlib
import Theorems.Thm_MertensTheorems_mertens_second

namespace ArtinPrimitiveRoots.MertensRecip

open Real Filter Topology

/-- Sum of reciprocals of primes up to `n`. -/
noncomputable def S (n : ℕ) : ℝ := ∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p

/-- Mertens error tends to zero. -/
lemma err_tendsto : ∃ M : ℝ, Tendsto (fun n : ℕ => S n - (log (log n) + M)) atTop (𝓝 0) := by
  obtain ⟨M, C, hC, h⟩ := MertensTheorems.mertens_second
  refine ⟨M, ?_⟩
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => C / log (n : ℝ)) atTop (𝓝 0) := hlog.const_div_atTop C
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact h n hn

/-- `log log ⌊y⌋ - log log y → 0`. -/
lemma loglog_floor : Tendsto (fun y : ℝ => log (log (⌊y⌋₊ : ℝ)) - log (log y)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => log ((⌊y⌋₊ : ℝ) / y)) atTop (𝓝 0) := by
    have := (continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp tendsto_nat_floor_div_atTop
    rw [log_one] at this
    exact this
  have h2 : Tendsto (fun y : ℝ => log ((⌊y⌋₊ : ℝ) / y) / log y) atTop (𝓝 0) := by
    have := h1.mul (tendsto_inv_atTop_zero.comp tendsto_log_atTop)
    simpa [div_eq_mul_inv] using this
  have h3 : Tendsto (fun y : ℝ => 1 + log ((⌊y⌋₊ : ℝ) / y) / log y) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add h2
  have h4 := ((continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp h3)
  rw [log_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop (3:ℝ)] with y hy
  have hy0 : 0 < y := by linarith
  have hf : (2:ℝ) ≤ (⌊y⌋₊ : ℝ) := by
    have : (2:ℕ) ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
    exact_mod_cast this
  have hf0 : (0:ℝ) < (⌊y⌋₊ : ℝ) := by linarith
  have hly : 0 < log y := log_pos (by linarith)
  have hlf : 0 < log (⌊y⌋₊ : ℝ) := log_pos (by linarith)
  simp only [Function.comp]
  rw [log_div hf0.ne' hy0.ne']
  have : 1 + (log (⌊y⌋₊ : ℝ) - log y) / log y = log (⌊y⌋₊ : ℝ) / log y := by
    field_simp; ring
  rw [this, log_div hlf.ne' hly.ne']

lemma sum_eq (x α β : ℝ) (hx : 1 ≤ x) (hαβ : α < β) :
    ∑ p ∈ (Finset.range (⌊x ^ β⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x ^ α < p), (1 : ℝ) / p
      = S ⌊x ^ β⌋₊ - S ⌊x ^ α⌋₊ := by
  have h0 : 0 ≤ x ^ α := rpow_nonneg (by linarith) _
  have hsub : (Finset.range (⌊x ^ α⌋₊ + 1)).filter Nat.Prime ⊆
      (Finset.range (⌊x ^ β⌋₊ + 1)).filter Nat.Prime := by
    apply Finset.filter_subset_filter
    apply Finset.range_subset_range.mpr
    have : ⌊x ^ α⌋₊ ≤ ⌊x ^ β⌋₊ :=
      Nat.floor_le_floor (rpow_le_rpow_of_exponent_le hx hαβ.le)
    omega
  have hset : (Finset.range (⌊x ^ β⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x ^ α < p) =
      (Finset.range (⌊x ^ β⌋₊ + 1)).filter Nat.Prime \
        (Finset.range (⌊x ^ α⌋₊ + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    have := Nat.floor_lt (n := p) h0
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun h => by have := this.mpr h3; omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, this.mp ?_⟩
      by_contra hc
      exact h3 ⟨by omega, h2⟩
  unfold S
  rw [hset, eq_sub_iff_add_eq, Finset.sum_sdiff hsub]

end ArtinPrimitiveRoots.MertensRecip

open Real Filter Topology ArtinPrimitiveRoots.MertensRecip

theorem solution (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    Tendsto (fun x : ℝ => ∑ p ∈ (Finset.range (⌊x ^ β⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ x ^ α < p), (1 : ℝ) / p) atTop (𝓝 (log (β / α))) := by
  obtain ⟨M, hM⟩ := err_tendsto
  have hβ : 0 < β := hα.trans hαβ
  have tα : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα
  have tβ : Tendsto (fun x : ℝ => x ^ β) atTop atTop := tendsto_rpow_atTop hβ
  have eα := hM.comp (tendsto_nat_floor_atTop.comp tα)
  have eβ := hM.comp (tendsto_nat_floor_atTop.comp tβ)
  have fα := loglog_floor.comp tα
  have fβ := loglog_floor.comp tβ
  have hall := (((eβ.sub eα).add fβ).sub fα).add
    (tendsto_const_nhds (x := log (β / α)))
  simp only [sub_zero, add_zero, zero_add] at hall
  refine hall.congr' ?_
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos hx
  rw [sum_eq x α β hx.le hαβ]
  simp only [Function.comp]
  have kα : log (log (x ^ α)) = log α + log (log x) := by
    rw [log_rpow hx0, log_mul hα.ne' hlx.ne']
  have kβ : log (log (x ^ β)) = log β + log (log x) := by
    rw [log_rpow hx0, log_mul hβ.ne' hlx.ne']
  rw [kα, kβ, log_div hβ.ne' hα.ne']
  ring
