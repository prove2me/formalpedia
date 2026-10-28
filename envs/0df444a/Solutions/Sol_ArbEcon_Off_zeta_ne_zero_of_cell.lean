-- Prove2me | solution 1 for ArbEcon.Off.zeta_ne_zero_of_cell
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:16.515688+00:00
-- url     : https://prove2.me/submissions/38081183-a68f-41f2-af99-874e310e73c4

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
import Theorems.Thm_ArbEcon_Off_emFinite_taylor_le
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





/-! ## T5. The Taylor model of the finite part. -/









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/











/-! ## T7. A zero-free cell. -/




theorem solution (K N p : ℕ) (hN : 1 ≤ N) (c s : ℂ) (r L a U E F : ℝ)
    (hc : 0 ≤ c.re) (hsc : ‖s - c‖ ≤ r) (hL : Real.log N ≤ L) (hrL : r * L ≤ 1) (ha : 0 < a)
    (hca : a ≤ c.im) (hsa : a ≤ s.im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U)
    (hE : ‖riemannZeta s - emFinite K s N‖ ≤ E) (hF : taylorErr K N p c r L a U + E ≤ F)
    (hmain : ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) + F < ‖Wk K N c 0‖) :
    riemannZeta s ≠ 0 := by
  intro hz
  set h := s - c with hh
  have hs : s = c + h := by rw [hh]; ring
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hsc
  have hT := emFinite_taylor_le K N p hN c h r L a U hc hsc hL hrL ha hca (by rw [← hs]; exact hsa)
    hU0 hU
  rw [← hs] at hT
  rw [hz, zero_sub, norm_neg] at hE
  -- the polynomial is small
  have hP : ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
      ≤ taylorErr K N p c r L a U + E := by
    have := norm_sub_le (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k))
      (emFinite K s N)
    have e : ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k) - emFinite K s N‖
        = ‖emFinite K s N - ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ :=
      norm_sub_rev _ _
    have := norm_le_insert' (∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k))
      (emFinite K s N)
    linarith
  -- ... but large
  have hbig : ‖Wk K N c 0‖ - ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ)
      ≤ ‖∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1)]
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, div_one]
    have hrest : ‖∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
        ≤ ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro k _
      simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_natCast]
      have hF : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hhk : ‖h‖ ^ k ≤ r ^ k := pow_le_pow_left₀ (norm_nonneg _) hsc k
      calc ‖h‖ ^ k * (1 / (k ! : ℝ) * ‖Wk K N c k‖) ≤ r ^ k * (1 / (k ! : ℝ) * ‖Wk K N c k‖) := by
            gcongr
        _ = ‖Wk K N c k‖ * r ^ k / (k ! : ℝ) := by ring
    have := norm_sub_norm_le (Wk K N c 0 + ∑ k ∈ Finset.Ico 1 (p + 1),
      h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)) (Wk K N c 0)
    have e2 : ‖Wk K N c 0 + ∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)
        - Wk K N c 0‖ = ‖∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖ := by
      congr 1; ring
    have := norm_sub_norm_le (Wk K N c 0)
      (-(∑ k ∈ Finset.Ico 1 (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)))
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  linarith
