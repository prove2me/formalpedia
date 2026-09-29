-- Prove2me | solution 1 for AnalyticGeometry.evalPadic_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:17:36.658495+00:00
-- url     : https://prove2.me/submissions/0ab5cb35-4c98-4370-bc2b-2ff654aaea23

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

open Filter Topology

lemma AGep_zpow_tendsto_zero {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    Tendsto (fun n : ℤ => s ^ n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℤ => n.toNat) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun n hn => by omega⟩)
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp ht
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  simp only [Function.comp_apply]
  rw [← zpow_natCast, Int.toNat_of_nonneg hn]

lemma AGep_decays_of_bounded {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) (f : LaurentSeries ℤ) (C : ℝ)
    (hC : ∀ n, |(f.coeff n : ℝ)| ≤ C) : AnalyticGeometry.DecaysAt s f := by
  have := (AGep_zpow_tendsto_zero h0 h1).const_mul C
  rw [mul_zero] at this
  refine squeeze_zero (fun n => ?_) (fun n => ?_) this
  · exact mul_nonneg (abs_nonneg _) (zpow_nonneg h0 n)
  · exact mul_le_mul_of_nonneg_right (hC n) (zpow_nonneg h0 n)

/-- A digit: a natural number `< p ^ k` congruent to `z` modulo `p ^ k` (if `‖z‖ ≤ 1`). -/
noncomputable def AGep_digit (p : ℕ) [Fact p.Prime] (k : ℕ) (z : ℚ_[p]) : ℕ :=
  if h : ‖z‖ ≤ 1 then PadicInt.appr (⟨z, h⟩ : ℤ_[p]) k else 0

lemma AGep_digit_lt (p : ℕ) [Fact p.Prime] (k : ℕ) (z : ℚ_[p]) : AGep_digit p k z < p ^ k := by
  unfold AGep_digit
  split_ifs with h
  · exact PadicInt.appr_lt _ _
  · exact pow_pos (Fact.out : p.Prime).pos k

lemma AGep_digit_spec (p : ℕ) [Fact p.Prime] (k : ℕ) (z : ℚ_[p]) (hz : ‖z‖ ≤ 1) :
    ‖z - (AGep_digit p k z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  unfold AGep_digit
  rw [dif_pos hz]
  have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ k).2 (PadicInt.appr_spec k ⟨z, hz⟩)
  exact h

/-- The remainder sequence of the `x`-adic digit expansion. -/
noncomputable def AGep_seq (p : ℕ) [Fact p.Prime] (k : ℕ) (x z : ℚ_[p]) : ℕ → ℚ_[p]
  | 0 => z
  | n + 1 => (AGep_seq p k x z n - (AGep_digit p k (AGep_seq p k x z n) : ℚ_[p])) / x

lemma AGep_seq_norm (p : ℕ) [Fact p.Prime] (k : ℕ) (x z : ℚ_[p]) (hx0 : x ≠ 0)
    (hk : (p : ℝ) ^ (-(k : ℤ)) ≤ ‖x‖) (hz : ‖z‖ ≤ 1) (n : ℕ) : ‖AGep_seq p k x z n‖ ≤ 1 := by
  induction n with
  | zero => simpa [AGep_seq] using hz
  | succ n ih =>
    simp only [AGep_seq]
    rw [norm_div]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    rw [div_le_one hxpos]
    exact (AGep_digit_spec p k _ ih).trans hk

lemma AGep_partial (p : ℕ) [Fact p.Prime] (k : ℕ) (x z : ℚ_[p]) (hx0 : x ≠ 0) (n : ℕ) :
    z = (∑ i ∈ Finset.range n, (AGep_digit p k (AGep_seq p k x z i) : ℚ_[p]) * x ^ i)
      + x ^ n * AGep_seq p k x z n := by
  induction n with
  | zero => simp [AGep_seq]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : AGep_seq p k x z (n + 1) * x =
        AGep_seq p k x z n - (AGep_digit p k (AGep_seq p k x z n) : ℚ_[p]) := by
      simp only [AGep_seq]
      field_simp
    linear_combination ih - (x ^ n) * this

lemma AGep_hasSum (p : ℕ) [Fact p.Prime] (k : ℕ) (x z : ℚ_[p]) (hx0 : x ≠ 0) (hx : ‖x‖ < 1)
    (hk : (p : ℝ) ^ (-(k : ℤ)) ≤ ‖x‖) (hz : ‖z‖ ≤ 1) :
    HasSum (fun i : ℕ => (AGep_digit p k (AGep_seq p k x z i) : ℚ_[p]) * x ^ i) z := by
  have hsum : Summable (fun i : ℕ => (AGep_digit p k (AGep_seq p k x z i) : ℚ_[p]) * x ^ i) := by
    refine Summable.of_norm_bounded (g := fun i : ℕ => ‖x‖ ^ i)
      (summable_geometric_of_lt_one (norm_nonneg _) hx) (fun i => ?_)
    rw [norm_mul, norm_pow]
    have h1 : ‖(AGep_digit p k (AGep_seq p k x z i) : ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) (AGep_digit p k (AGep_seq p k x z i) : ℤ)
      simpa using this
    calc ‖(AGep_digit p k (AGep_seq p k x z i) : ℚ_[p])‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ = ‖x‖ ^ i := one_mul _
  refine (hsum.hasSum_iff_tendsto_nat).2 ?_
  have hrem : Tendsto (fun n : ℕ => x ^ n * AGep_seq p k x z n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hx)
    rw [norm_mul, norm_pow]
    calc ‖x‖ ^ n * ‖AGep_seq p k x z n‖ ≤ ‖x‖ ^ n * 1 :=
          mul_le_mul_of_nonneg_left (AGep_seq_norm p k x z hx0 hk hz n)
            (pow_nonneg (norm_nonneg _) _)
      _ = ‖x‖ ^ n := mul_one _
  have := (tendsto_const_nhds (x := z)).sub hrem
  rw [sub_zero] at this
  refine this.congr (fun n => ?_)
  have h := AGep_partial p k x z hx0 n
  rw [sub_eq_iff_eq_add]
  exact h

open AnalyticGeometry in
theorem solution (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (p : ℕ) [hp : Fact p.Prime]
    (x : ℚ_[p]) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (y : ℚ_[p]) :
    ∃ f ∈ zLaurentGT r,
      Summable (fun n : ℤ => (f.coeff n : ℚ_[p]) * x ^ n) ∧
        ∑' n : ℤ, (f.coeff n : ℚ_[p]) * x ^ n = y := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  -- precision `k` with `p ^ (-k) ≤ ‖x‖`
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hxpos (inv_lt_one_of_one_lt₀ hp1)
  have hk' : (p : ℝ) ^ (-(k : ℤ)) ≤ ‖x‖ := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hk.le
  -- shift `N` with `‖x ^ N * y‖ ≤ 1`
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by positivity : (0:ℝ) < ‖y‖ + 1)) hx
  set z : ℚ_[p] := x ^ N * y with hzdef
  have hz : ‖z‖ ≤ 1 := by
    rw [hzdef, norm_mul, norm_pow]
    have h1 : ‖x‖ ^ N * (‖y‖ + 1) ≤ 1 := by
      have := mul_lt_mul_of_pos_right hN (by positivity : (0:ℝ) < ‖y‖ + 1)
      rw [inv_mul_cancel₀ (by positivity)] at this
      exact this.le
    nlinarith [pow_nonneg (norm_nonneg x) N, norm_nonneg y]
  set d : ℕ → ℕ := fun i => AGep_digit p k (AGep_seq p k x z i) with hd
  let c : ℤ → ℤ := fun n => if 0 ≤ n + N then (d (n + N).toNat : ℤ) else 0
  have hc : BddBelow (Function.support c) := by
    refine ⟨-(N : ℤ), fun n hn => ?_⟩
    by_contra hlt
    apply hn
    simp only [c]
    rw [if_neg (by omega)]
  let f : LaurentSeries ℤ := HahnSeries.ofSuppBddBelow c hc
  have hfc : ∀ n, f.coeff n = c n := fun n => rfl
  have hmem : f ∈ zLaurentGT r := by
    refine ⟨(r + 1) / 2, by linarith,
      AGep_decays_of_bounded (by linarith) (by linarith) f (p ^ k : ℕ) (fun n => ?_)⟩
    rw [hfc]
    simp only [c]
    split_ifs
    · simp only [Int.cast_natCast, Nat.abs_cast]
      exact_mod_cast (AGep_digit_lt p k _).le
    · simp
  -- the sum over `ℤ` is the shifted sum over `ℕ`
  have hN0 : x ^ N ≠ 0 := pow_ne_zero _ hx0
  have hS : HasSum (fun i : ℕ => ((d i : ℚ_[p]) * x ^ i) * (x ^ N)⁻¹) (z * (x ^ N)⁻¹) :=
    (AGep_hasSum p k x z hx0 hx hk' hz).mul_right _
  have hzy : z * (x ^ N)⁻¹ = y := by
    rw [hzdef]; field_simp
  rw [hzy] at hS
  let g : ℕ → ℤ := fun i => (i : ℤ) - N
  have hg : Function.Injective g := fun a b h => by simp only [g] at h; omega
  have hcomp : (fun n : ℤ => (f.coeff n : ℚ_[p]) * x ^ n) ∘ g =
      fun i : ℕ => ((d i : ℚ_[p]) * x ^ i) * (x ^ N)⁻¹ := by
    funext i
    simp only [Function.comp_apply, g, hfc, c]
    rw [if_pos (by omega)]
    have : ((i : ℤ) - N + N).toNat = i := by omega
    rw [this, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]
    push_cast
    ring
  have hF : HasSum (fun n : ℤ => (f.coeff n : ℚ_[p]) * x ^ n) y := by
    rw [← hg.hasSum_iff]
    · rw [hcomp]; exact hS
    · intro n hn
      have : ¬ (0 ≤ n + N) := by
        intro h
        apply hn
        exact ⟨(n + N).toNat, by simp only [g]; omega⟩
      simp only [hfc, c]
      rw [if_neg this]
      simp
  exact ⟨f, hmem, hF.summable, hF.tsum_eq⟩
