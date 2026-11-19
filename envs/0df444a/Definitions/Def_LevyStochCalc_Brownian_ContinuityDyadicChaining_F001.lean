-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001
-- name    : LevyStochCalc_Brownian_ContinuityDyadicChaining_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:12:30.173644+00:00
-- url     : https://prove2.me/theorems/3d59f506-1919-4bbd-b083-7fc52553be85
-- title:
--   Source declarations: LevyStochCalc.Brownian.ContinuityDyadicChaining
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ContinuityDyadicChaining. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F000
import Definitions.Def_SourceProof_8cc83ed884458283276d879b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

/-- Dyadic rationals are closed under adding an integer. -/
lemma add_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x + (j : ℝ) ∈ dyadicRationals := by
  obtain ⟨k, n, rfl⟩ := hx
  refine ⟨k + j * 2 ^ n, n, ?_⟩
  rw [zpow_neg, zpow_natCast]
  push_cast
  field_simp
/-- Dyadic rationals are closed under subtracting an integer. -/
lemma sub_intCast_mem_dyadicRationals {x : ℝ} (hx : x ∈ dyadicRationals) (j : ℤ) :
    x - (j : ℝ) ∈ dyadicRationals := by
  have := add_intCast_mem_dyadicRationals hx (-j)
  simpa [sub_eq_add_neg] using this
/-- For every `t : ℝ`, there is a sequence of dyadic rationals strictly
increasing to `t`. Wrapper around `Dense.exists_seq_strictMono_tendsto` +
`dense_dyadicRationals`. -/
lemma exists_seq_dyadic_tendsto (t : ℝ) :
    ∃ u : ℕ → ℝ, StrictMono u
      ∧ (∀ n, u n ∈ Set.Iio t ∩ dyadicRationals)
      ∧ Filter.Tendsto u Filter.atTop (nhds t) :=
  _root_.Prove2MeSourceProof.h_8cc83ed884458283276d879b.exists_seq_strictMono_tendsto t
/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/

/-- Level-`n` dyadic truncation `⌊x·2ⁿ⌋ / 2ⁿ` — the largest level-`n` dyadic
`≤ x`. -/
noncomputable def dyadicTrunc (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ : ℝ) / 2 ^ n
lemma dyadicTrunc_mem_dyadicRationals (n : ℕ) (x : ℝ) :
    dyadicTrunc n x ∈ dyadicRationals := by
  refine ⟨⌊x * 2 ^ n⌋, n, ?_⟩
  rw [dyadicTrunc, zpow_neg, zpow_natCast, div_eq_mul_inv]
lemma dyadicTrunc_le (n : ℕ) (x : ℝ) : dyadicTrunc n x ≤ x := by
  rw [dyadicTrunc, div_le_iff₀ (by positivity)]
  exact Int.floor_le _
/-- `2⌊y⌋ ≤ ⌊2y⌋ ≤ 2⌊y⌋ + 1`. -/
lemma floor_two_mul_bounds (y : ℝ) :
    2 * ⌊y⌋ ≤ ⌊2 * y⌋ ∧ ⌊2 * y⌋ ≤ 2 * ⌊y⌋ + 1 := by
  refine ⟨?_, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le y]
  · have h2 : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith [Int.lt_floor_add_one y]
    omega
/-- **Single refinement step.** For `x ∈ [0,1]`, the level-`(n+1)` truncation
differs from the level-`n` truncation by at most one consecutive level-`(n+1)`
dyadic increment, hence `|f(trunc_{n+1} x) − f(trunc_n x)| ≤ b (n+1)`. -/
lemma dyadicTrunc_succ_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1) := by
  set k : ℤ := ⌊x * 2 ^ n⌋ with hk
  set j : ℤ := ⌊x * 2 ^ (n + 1)⌋ with hj
  have hjk : j = ⌊2 * (x * 2 ^ n)⌋ := by rw [hj]; congr 1; rw [pow_succ]; ring
  obtain ⟨hlo, hhi⟩ := floor_two_mul_bounds (x * 2 ^ n)
  rw [← hjk] at hlo hhi
  have hk0 : 0 ≤ k := by
    rw [hk]; apply Int.floor_nonneg.mpr; positivity
  -- Truncations expressed over the common denominator `2^(n+1)`.
  have hDn : dyadicTrunc n x = ((2 * k : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hk, pow_succ]; push_cast; ring
  have hDn1 : dyadicTrunc (n + 1) x = ((j : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hj]
  rcases (by omega : j = 2 * k ∨ j = 2 * k + 1) with hjeq | hjeq
  · -- No refinement: the two truncations coincide.
    rw [hDn1, hDn, hjeq, sub_self, abs_zero]
    exact hb (n + 1)
  · -- One refinement step `(2k) → (2k+1)` at level `n+1`.
    have hbound : 2 * k + 1 ≤ (2 : ℤ) ^ (n + 1) := by
      have hjle : (j : ℝ) ≤ x * 2 ^ (n + 1) := Int.floor_le _
      have hj_le : (j : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
        le_trans hjle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (n + 1)])
      have : (j : ℤ) ≤ (2 : ℤ) ^ (n + 1) := by exact_mod_cast hj_le
      omega
    have hap := hf (n + 1) hn (2 * k) (by omega) hbound
    rw [hDn1, hDn, hjeq]
    exact_mod_cast hap
/-- **Telescoping bound across levels.** For `x ∈ [0,1]` and `m ≤ L`, the
truncation increment from level `m` to level `L` is bounded by the sum of the
per-level bounds `b (m+1) + ⋯ + b L`. -/
lemma dyadicTrunc_telescope {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
    ∀ L, m ≤ L → |f (dyadicTrunc L x) - f (dyadicTrunc m x)|
      ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    rw [sub_self, abs_zero, Finset.Ico_self, Finset.sum_empty]
  | succ L hmL ih =>
    calc |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc m x)|
        ≤ |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc L x)|
          + |f (dyadicTrunc L x) - f (dyadicTrunc m x)| := abs_sub_le _ _ _
      _ ≤ b (L + 1) + ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
          refine add_le_add ?_ ih
          exact dyadicTrunc_succ_step hb hf (by omega) hx0 hx1
      _ = ∑ n ∈ Finset.Ico (m + 1) (L + 2), b n := by
          rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ L + 1)]
          ring
/-- **Cross-point step at a fixed level.** For `0 ≤ s ≤ t ≤ 1` with
`t − s ≤ 2^{-m}`, the level-`m` truncations of `s` and `t` are equal or adjacent
level-`m` dyadics, so `|f(trunc_m s) − f(trunc_m t)| ≤ b m`. -/
lemma dyadicTrunc_near_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m := by
  set ks : ℤ := ⌊s * 2 ^ m⌋ with hks
  set kt : ℤ := ⌊t * 2 ^ m⌋ with hkt
  have hks0 : 0 ≤ ks := by rw [hks]; apply Int.floor_nonneg.mpr; positivity
  have hmono : ks ≤ kt := by
    rw [hks, hkt]; apply Int.floor_le_floor
    exact mul_le_mul_of_nonneg_right hst (by positivity)
  have hclose' : t * 2 ^ m ≤ s * 2 ^ m + 1 := by
    have hmul : (t - s) * 2 ^ m ≤ 1 := by
      calc (t - s) * 2 ^ m ≤ (1 / 2) ^ m * 2 ^ m :=
            mul_le_mul_of_nonneg_right hclose (by positivity)
        _ = 1 := by rw [div_pow, one_pow, div_mul_cancel₀]; positivity
    nlinarith
  have hkt_le : kt ≤ ks + 1 := by
    rw [hkt, hks]
    calc ⌊t * 2 ^ m⌋ ≤ ⌊s * 2 ^ m + 1⌋ := Int.floor_le_floor (by linarith)
      _ = ⌊s * 2 ^ m⌋ + 1 := Int.floor_add_one _
  have hTs : dyadicTrunc m s = ((ks : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hks]
  have hTt : dyadicTrunc m t = ((kt : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hkt]
  rcases (by omega : kt = ks ∨ kt = ks + 1) with he | he
  · rw [hTs, hTt, he, sub_self, abs_zero]; exact hb m
  · have hbnd : ks + 1 ≤ (2 : ℤ) ^ m := by
      have hktle : (kt : ℝ) ≤ t * 2 ^ m := Int.floor_le _
      have hkt_le2 : (kt : ℝ) ≤ (2 : ℝ) ^ m :=
        le_trans hktle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m])
      have : (kt : ℤ) ≤ (2 : ℤ) ^ m := by exact_mod_cast hkt_le2
      omega
    have hap := hf m hm ks hks0 hbnd
    rw [hTs, hTt, he, abs_sub_comm]
    exact_mod_cast hap
/-- A dyadic rational coincides with its own level-`L` truncation for all
sufficiently large `L`. -/
lemma dyadicTrunc_eventually_eq {s : ℝ} (hs : s ∈ dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s := by
  obtain ⟨k, n, hkn⟩ := hs
  refine ⟨n, fun L hL => ?_⟩
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - n) * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hL]
  have hsL : s * 2 ^ L = ((k * 2 ^ (L - n) : ℤ) : ℝ) := by
    rw [hkn, zpow_neg, zpow_natCast, hpow]
    push_cast
    field_simp
  rw [dyadicTrunc, hsL, Int.floor_intCast, hkn, zpow_neg, zpow_natCast, hpow]
  push_cast
  field_simp
/-- Finite geometric partial sum bounded by the infinite tail
`∑_{a ≤ n < b} rⁿ ≤ rᵃ / (1 − r)` for `0 ≤ r < 1`. -/
lemma sum_Ico_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, r ^ n ≤ r ^ a / (1 - r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity)
    (summable_geometric_of_lt_one hr0 hr1)
/-- **Dyadic scale selection.** For `0 < d ≤ 1` there is `m` with
`(1/2)^{m+1} < d ≤ (1/2)^m`. -/
lemma exists_dyadic_scale {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < d :=
    exists_pow_lt_of_lt_one hd0 (by norm_num)
  classical
  have hspec : (1 / 2 : ℝ) ^ Nat.find hex < d := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hpos]; exact hspec
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_lt] at hmin
    exact hmin
/-- `((1/2)^α)^m ≤ 2^α · d^α` when `(1/2)^{m+1} < d`. Converts the geometric
level factor `r^m = ((1/2)^α)^m` into a Hölder factor in `d`. -/
lemma rpow_half_pow_le {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
    (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
    ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α := by
  have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hstep : (1 / 2 : ℝ) ^ m < 2 * d := by
    have he : (1 / 2 : ℝ) ^ m = 2 * (1 / 2) ^ (m + 1) := by rw [pow_succ]; ring
    rw [he]; linarith
  have hr_eq : ((1 / 2 : ℝ) ^ α) ^ m = ((1 / 2 : ℝ) ^ m) ^ α := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) m,
        ← Real.rpow_natCast (1 / 2 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_comm]
  rw [hr_eq]
  calc ((1 / 2 : ℝ) ^ m) ^ α
      ≤ (2 * d) ^ α :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hstep) (le_of_lt hα)
    _ = (2 : ℝ) ^ α * d ^ α := Real.mul_rpow (by norm_num) (le_of_lt hdpos)
end LevyStochCalc.Brownian.Continuity


