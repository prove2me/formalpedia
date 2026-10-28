-- Prove2me | solution 1 for ArbEcon.Off.emCorr_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:09.273148+00:00
-- url     : https://prove2.me/submissions/a353273b-30d5-4642-ade5-e07e67017d93

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_Off_norm_poch_sub_le
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh

/-  EMZetaOfflineSlab.lean -- lane offline: zero-free cells OFF the critical line by a Taylor model
    of the Euler-Maclaurin finite part (the analysis behind a `SlabClear` certificate).

    For a center `c = σc + i tc` (`σc ≥ 0`) and a point `s = c + h`, `‖h‖ ≤ r`:

      T1.  `exp_taylor_le`        -- `‖e^w - Σ_{k≤p} w^k/k!‖ ≤ ‖w‖^(p+1) (p+2)/((p+1)!(p+1))`, `‖w‖ ≤ 1`;
      T2.  `natCpow_neg_add`      -- `n^(-(c+h)) = n^(-c) e^(-h log n)`;
      T3.  `norm_poch_sub_le`     -- `‖(c+h)_k - (c)_k‖ ≤ (U+r)^k - U^k` when every `‖c + j‖ ≤ U`;
      T4.  `emCorr_sub_le`        -- the correction factor moves by at most
                                     `δ = N r / a² + Σ_{i<2K-1} |B_{i+2}|/(i+2)! ((U+r)^(i+1) - U^(i+1)) / N^(i+1)`
                                     (`a ≤ Im c`, `a ≤ Im s`);
      T5.  `emFinite_taylor_le`   -- THE TAYLOR MODEL:
                                     `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! · W_k‖ ≤ Err`, where
                                     `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)` and
                                     `Err = C_p (r L)^(p+1) ((N-1) + ‖emCorr(c)‖) + 3 δ`, `L ≥ log N`;
      T6.  `em_remainder_region`  -- the order-(2K+1) remainder uniformly on `1/2 ≤ Re s ≤ 1`,
                                     `0 ≤ Im s ≤ B`;
      T7.  `zeta_ne_zero_of_cell` -- a zero at `s` would force `‖Σ_k h^k …‖ ≤ Err + E`; so
                                     `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + Err + E` rules it out.

    conjecture1_proved = False.  A finite, local nonvanishing argument; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off

/-! ## T1. The complex exponential Taylor remainder. -/







/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/



theorem solution (K N : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r a U : ℝ) (hr : ‖h‖ ≤ r) (ha : 0 < a)
    (hca : a ≤ c.im) (hsa : a ≤ (c + h).im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emCorr K (c + h) N - emCorr K c N‖ ≤ corrVar K N r a U := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  have hc1 : c - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  have hs1 : c + h - 1 ≠ 0 := by
    intro h0; have := congrArg Complex.im h0
    have hch : (c + h).im = c.im + h.im := Complex.add_im c h
    simp at this; linarith
  have hnc : a ≤ ‖c - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_pos (by linarith)]; exact hca
  have hns : a ≤ ‖c + h - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.one_im, sub_zero]
    rw [abs_of_pos (by linarith)]; exact hsa
  unfold emCorr corrVar
  have e : ((N : ℂ) / (c + h - 1) + 1 / 2
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) * poch (c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
      - ((N : ℂ) / (c - 1) + 1 / 2
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) * poch c (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
      = (N : ℂ) * (-h) / ((c + h - 1) * (c - 1))
        + ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) / ((i + 2)! : ℂ) * (poch (c + h) (i + 1) - poch c (i + 1))
              / (N : ℂ) ^ (i + 1) := by
    have hfr : (N : ℂ) / (c + h - 1) - (N : ℂ) / (c - 1) = (N : ℂ) * (-h) / ((c + h - 1) * (c - 1)) := by
      field_simp; ring
    have hsum : ∑ i ∈ Finset.range (2 * K - 1),
          ((bernoulli (i + 2) : ℂ) * poch (c + h) (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1)
            - (bernoulli (i + 2) : ℂ) * poch c (i + 1) / ((i + 2)! : ℂ) / (N : ℂ) ^ (i + 1))
        = ∑ i ∈ Finset.range (2 * K - 1),
            (bernoulli (i + 2) : ℂ) / ((i + 2)! : ℂ) * (poch (c + h) (i + 1) - poch c (i + 1))
              / (N : ℂ) ^ (i + 1) := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [← hsum, Finset.sum_sub_distrib, ← hfr]; ring
  rw [e]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_neg, norm_mul, Complex.norm_natCast]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : a * a ≤ ‖c + h - 1‖ * ‖c - 1‖ := mul_le_mul hns hnc ha.le (norm_nonneg _)
    have h2 : (N : ℝ) * ‖h‖ ≤ (N : ℝ) * r := mul_le_mul_of_nonneg_left hr hNR.le
    calc (N : ℝ) * ‖h‖ * a ^ 2 ≤ (N : ℝ) * r * a ^ 2 := by gcongr
      _ = (N : ℝ) * r * (a * a) := by ring
      _ ≤ (N : ℝ) * r * (‖c + h - 1‖ * ‖c - 1‖) := by gcongr
  · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro i hi
    have hi' : i + 1 ≤ 2 * K := by
      have := Finset.mem_range.mp hi; omega
    have hp := norm_poch_sub_le c h r U hr hU0 (i + 1) (fun j hj => hU j (by omega))
    have hb : ‖((bernoulli (i + 2) : ℚ) : ℂ)‖ = |((bernoulli (i + 2) : ℚ) : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast, hb]
    have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hNp : (0 : ℝ) < (N : ℝ) ^ (i + 1) := by positivity
    gcongr
