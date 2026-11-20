-- Prove2me | Definitions.Def_SourceProof_acac0f8ce0c5f96fd64efb3a
-- name    : SourceProof_acac0f8ce0c5f96fd64efb3a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:52:36.177612+00:00
-- url     : https://prove2.me/theorems/a4160b18-0003-48aa-aea8-540712544fea
-- title:
--   LevyStochCalc source module: SourceProof_acac0f8ce0c5f96fd64efb3a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining` comes from the `LevyStochCalc.Brownian.ContinuityDyadicChaining` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001

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

/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/


theorem _root_.Prove2MeSourceProof.h_acac0f8ce0c5f96fd64efb3a {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have h1r : 0 < 1 - r := by linarith
  set b : ℕ → ℝ := fun n => C * r ^ n with hb_def
  have hb : ∀ n, 0 ≤ b n := fun n => by simp only [hb_def]; positivity
  set A : ℝ := C * (1 + 2 * r / (1 - r)) with hA_def
  have hA0 : 0 ≤ A := by
    apply mul_nonneg hC
    have : 0 ≤ 2 * r / (1 - r) := div_nonneg (by positivity) (le_of_lt h1r)
    linarith
  have h2α : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  -- Sum bound: `∑_{Ico (m+1) (L+1)} b ≤ C·r^{m+1}/(1-r)`.
  have hsum : ∀ m L : ℕ, ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n
      ≤ C * r ^ (m + 1) / (1 - r) := by
    intro m L
    simp only [hb_def]
    rw [← Finset.mul_sum]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hC
    exact LevyStochCalc.Brownian.Continuity.sum_Ico_geometric_le (le_of_lt hr0) hr1 (m + 1) (L + 1)
  -- Core bound for an ordered pair `a ≤ c`.
  have core : ∀ a c, a ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals → c ∈ LevyStochCalc.Brownian.Continuity.dyadicRationals →
      0 ≤ a → c ≤ 1 → a ≤ c → c - a ≤ (1 / 2 : ℝ) ^ N →
      |f a - f c| ≤ (A * 2 ^ α) * (c - a) ^ α := by
    intro a c ha hc ha0 hc1 hac hgap
    rcases eq_or_lt_of_le hac with hac' | hac'
    · subst hac'; simp [Real.zero_rpow hα.ne']
    set d : ℝ := c - a with hd_def
    have hd0 : 0 < d := by simp only [hd_def]; linarith
    have hNle1 : (1 / 2 : ℝ) ^ N ≤ 1 := by
      apply pow_le_one₀ (by norm_num) (by norm_num)
    have hd1 : d ≤ 1 := le_trans hgap hNle1
    obtain ⟨m, hm1, hm2⟩ := LevyStochCalc.Brownian.Continuity.exists_dyadic_scale hd0 hd1
    have hmN : N ≤ m := by
      by_contra hlt
      have hNm1 : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (m + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [le_trans hgap hNm1, hm1]
    obtain ⟨Ls, hLs⟩ := LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq ha
    obtain ⟨Lt, hLt⟩ := LevyStochCalc.Brownian.Continuity.dyadicTrunc_eventually_eq hc
    set L : ℕ := max (max Ls Lt) m with hL_def
    have hsL : LevyStochCalc.Brownian.Continuity.dyadicTrunc L a = a :=
      hLs L (le_trans (le_max_left _ _) (le_max_left _ _))
    have htL : LevyStochCalc.Brownian.Continuity.dyadicTrunc L c = c :=
      hLt L (le_trans (le_max_right _ _) (le_max_left _ _))
    have hmL : m ≤ L := le_max_right _ _
    have hTa := LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope hb hf ha0 (le_trans hac hc1) (by omega) L hmL
    have hTc := LevyStochCalc.Brownian.Continuity.dyadicTrunc_telescope hb hf (le_trans ha0 hac) hc1 (by omega) L hmL
    rw [hsL] at hTa
    rw [htL] at hTc
    have hNear := LevyStochCalc.Brownian.Continuity.dyadicTrunc_near_step hb hf hmN ha0 hc1 hac hm2
    -- Triangle: split through the two level-m truncations.
    have htri : |f a - f c|
        ≤ |f a - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a)|
          + |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m c)|
          + |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m c) - f c| := by
      calc |f a - f c|
          ≤ |f a - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a)| + |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a) - f c| :=
            abs_sub_le _ _ _
        _ ≤ |f a - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a)|
            + (|f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m a) - f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m c)|
              + |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m c) - f c|) := by
            gcongr; exact abs_sub_le _ _ _
        _ = _ := by ring
    have hTc' : |f (LevyStochCalc.Brownian.Continuity.dyadicTrunc m c) - f c|
        ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
      rw [abs_sub_comm]; exact hTc
    -- Combine the three pieces.
    have hsumbnd := hsum m L
    have hbm : b m = C * r ^ m := rfl
    have key : |f a - f c| ≤ A * r ^ m := by
      have hchain : |f a - f c|
          ≤ (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
            + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) := by
        refine le_trans htri ?_
        gcongr
      refine le_trans hchain ?_
      have hnum : (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
          + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n)
          ≤ C * r ^ (m + 1) / (1 - r) + C * r ^ m + C * r ^ (m + 1) / (1 - r) := by
        linarith [hsum m L, hbm]
      refine le_trans hnum (le_of_eq ?_)
      rw [hA_def]
      field_simp
      ring
    refine le_trans key ?_
    rw [show A * 2 ^ α * d ^ α = A * (2 ^ α * d ^ α) from by ring]
    apply mul_le_mul_of_nonneg_left _ hA0
    rw [hr_def]
    exact LevyStochCalc.Brownian.Continuity.rpow_half_pow_le hα m hm1
  -- Dispatch by the order of `s, t`.
  refine ⟨A * 2 ^ α, by positivity, ?_⟩
  intro s hs t ht hs0 hs1 ht0 ht1 hclose
  rcases le_total s t with hst | hst
  · have hgap : t - s ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s), abs_sub_comm]; exact hclose
    have heq : |s - t| = t - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [heq]
    exact core s t hs ht hs0 ht1 hst hgap
  · have hgap : s - t ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]; exact hclose
    have heq : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [heq, abs_sub_comm]
    exact core t s ht hs ht0 hs1 hst hgap
end LevyStochCalc.Brownian.Continuity


