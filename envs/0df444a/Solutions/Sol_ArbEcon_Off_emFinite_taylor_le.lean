-- Prove2me | solution 1 for ArbEcon.Off.emFinite_taylor_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:58:24.735959+00:00
-- url     : https://prove2.me/submissions/e6aab3d0-c234-47ce-aaae-f52d76bccea3

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
import Theorems.Thm_ArbEcon_Off_emCorr_sub_le
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

namespace ArbEcon

namespace Off

/-! ## T1. The complex exponential Taylor remainder. -/



theorem Cp_nonneg (p : ℕ) : 0 ≤ Cp p := by unfold Cp; positivity

theorem exp_taylor_le (w : ℂ) (hw : ‖w‖ ≤ 1) (p : ℕ) :
    ‖Complex.exp w - ∑ k ∈ Finset.range (p + 1), w ^ k / (k ! : ℂ)‖ ≤ ‖w‖ ^ (p + 1) * Cp p := by
  have h := Complex.exp_bound hw (n := p + 1) (by omega)
  refine le_trans h (le_of_eq ?_)
  unfold Cp
  push_cast
  field_simp
  ring

/-! ## T2. Shifting the exponent. -/

theorem natCpow_neg_add (n : ℕ) (hn : 1 ≤ n) (c h : ℂ) :
    (n : ℂ) ^ (-(c + h)) = (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))) := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hnpos.le]
  rw [Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne, hlog, ← Complex.exp_add]
  congr 1
  ring

theorem norm_natCpow_neg_le_one (n : ℕ) (hn : 1 ≤ n) (c : ℂ) (hc : 0 ≤ c.re) :
    ‖(n : ℂ) ^ (-c)‖ ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/





/-! ## T5. The Taylor model of the finite part. -/





theorem exp_one_le_three : Real.exp 1 ≤ 3 := by
  have := Real.exp_one_lt_d9
  linarith



/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/











/-! ## T7. A zero-free cell. -/





end Off

end ArbEcon


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







theorem solution (K N p : ℕ) (hN : 1 ≤ N) (c h : ℂ) (r L a U : ℝ) (hc : 0 ≤ c.re)
    (hr : ‖h‖ ≤ r) (hL : Real.log N ≤ L) (hrL : r * L ≤ 1) (ha : 0 < a) (hca : a ≤ c.im)
    (hsa : a ≤ (c + h).im) (hU0 : 0 ≤ U) (hU : ∀ j, j < 2 * K → ‖c + j‖ ≤ U) :
    ‖emFinite K (c + h) N
        - ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)‖
      ≤ taylorErr K N p c r L a U := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hL0 : 0 ≤ L := le_trans hlogN hL
  -- per-term exponential remainder
  have hterm : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
          - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
        ≤ (r * L) ^ (p + 1) * Cp p := by
    intro n hn1 hnN
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlognL : Real.log n ≤ L :=
      le_trans (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hnN)) hL
    have hw : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ r * L := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogn]
      exact mul_le_mul hr hlognL hlogn hr0
    have hw1 : ‖-(h * ((Real.log n : ℝ) : ℂ))‖ ≤ 1 := le_trans hw hrL
    refine le_trans (exp_taylor_le _ hw1 p) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw _) (Cp_nonneg p)
  -- the polynomial part, rewritten termwise
  have hpow : ∀ (x : ℝ) (k : ℕ), (-(h * (x : ℂ))) ^ k / (k ! : ℂ)
      = h ^ k * ((-1) ^ k / (k ! : ℂ) * (x : ℂ) ^ k) := by
    intro x k; rw [neg_pow, mul_pow]; ring
  have hpoly : ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ) * Wk K N c k)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))
        + (N : ℂ) ^ (-c) * emCorr K c N
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) := by
    simp only [Wk, mul_add, Finset.sum_add_distrib]
    congr 1
    · calc ∑ k ∈ Finset.range (p + 1), h ^ k * ((-1) ^ k / (k ! : ℂ)
              * ∑ n ∈ Finset.Ico 1 N, ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))
          = ∑ k ∈ Finset.range (p + 1), ∑ n ∈ Finset.Ico 1 N,
              h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) := by
            apply Finset.sum_congr rfl; intro k _; rw [Finset.mul_sum, Finset.mul_sum]
        _ = ∑ n ∈ Finset.Ico 1 N, ∑ k ∈ Finset.range (p + 1),
              h ^ k * ((-1) ^ k / (k ! : ℂ) * (((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-c))) :=
            Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl; intro n _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _
            rw [hpow]; ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [hpow]; ring
  -- the finite part at c + h
  have hfin : emFinite K (c + h) N
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) * emCorr K (c + h) N := by
    unfold emFinite
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      exact natCpow_neg_add n (Finset.mem_Ico.mp hn).1 c h
    · rw [natCpow_neg_add N hN c h]
  rw [hpoly, hfin]
  set eN := Complex.exp (-(h * ((Real.log N : ℝ) : ℂ))) with heN
  set PN := ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log N : ℝ) : ℂ))) ^ k / (k ! : ℂ) with hPN
  have e : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
        + (N : ℂ) ^ (-c) * eN * emCorr K (c + h) N
        - ((∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
            * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))
          + (N : ℂ) ^ (-c) * emCorr K c N * PN)
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)))
        + ((N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)
          + (N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)) := by
    have hsd : (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * Complex.exp (-(h * ((Real.log n : ℝ) : ℂ))))
          - ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c)
              * ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)
        = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [← hsd]
    ring
  rw [e]
  have hNc : ‖(N : ℂ) ^ (-c)‖ ≤ 1 := norm_natCpow_neg_le_one N hN c hc
  -- the three pieces
  have p1 : ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
      ≤ ((N : ℝ) - 1) * ((r * L) ^ (p + 1) * Cp p) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hle : ∀ n ∈ Finset.Ico 1 N, ‖(n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
        - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
          ≤ (r * L) ^ (p + 1) * Cp p := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Ico.mp hn
      rw [norm_mul]
      have := hterm n hn1 hnN.le
      have hn' := norm_natCpow_neg_le_one n hn1 c hc
      calc ‖(n : ℂ) ^ (-c)‖ * ‖Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ)‖
          ≤ 1 * ((r * L) ^ (p + 1) * Cp p) := by
            gcongr
        _ = (r * L) ^ (p + 1) * Cp p := one_mul _
    refine le_trans (Finset.sum_le_sum hle) (le_of_eq ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    push_cast [Nat.cast_sub hN]
    ring
  have p2 : ‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
      ≤ ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) := by
    rw [norm_mul, norm_mul]
    have := hterm N hN le_rfl
    calc ‖(N : ℂ) ^ (-c)‖ * ‖emCorr K c N‖ * ‖eN - PN‖
        ≤ 1 * ‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) := by gcongr
      _ = _ := by ring
  have p3 : ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖ ≤ 3 * corrVar K N r a U := by
    rw [norm_mul, norm_mul]
    have hv := emCorr_sub_le K N hN c h r a U hr ha hca hsa hU0 hU
    have heNle : ‖eN‖ ≤ 3 := by
      rw [heN, Complex.norm_exp]
      have hre : (-(h * ((Real.log N : ℝ) : ℂ))).re ≤ 1 := by
        have h1 : (-(h * ((Real.log N : ℝ) : ℂ))).re ≤ ‖-(h * ((Real.log N : ℝ) : ℂ))‖ :=
          Complex.re_le_norm _
        have h2 : ‖-(h * ((Real.log N : ℝ) : ℂ))‖ ≤ r * L := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlogN]
          exact mul_le_mul hr hL hlogN hr0
        linarith
      exact le_trans (Real.exp_le_exp.mpr hre) exp_one_le_three
    calc ‖(N : ℂ) ^ (-c)‖ * ‖eN‖ * ‖emCorr K (c + h) N - emCorr K c N‖
        ≤ 1 * 3 * corrVar K N r a U := by gcongr
      _ = 3 * corrVar K N r a U := by ring
  unfold taylorErr
  calc _ ≤ ‖∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-c) * (Complex.exp (-(h * ((Real.log n : ℝ) : ℂ)))
            - ∑ k ∈ Finset.range (p + 1), (-(h * ((Real.log n : ℝ) : ℂ))) ^ k / (k ! : ℂ))‖
        + (‖(N : ℂ) ^ (-c) * emCorr K c N * (eN - PN)‖
          + ‖(N : ℂ) ^ (-c) * eN * (emCorr K (c + h) N - emCorr K c N)‖) :=
        le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ((N : ℝ) - 1) * ((r * L) ^ (p + 1) * Cp p)
        + (‖emCorr K c N‖ * ((r * L) ^ (p + 1) * Cp p) + 3 * corrVar K N r a U) := by
        gcongr
    _ = Cp p * (r * L) ^ (p + 1) * (((N : ℝ) - 1) + ‖emCorr K c N‖) + 3 * corrVar K N r a U := by
        ring
