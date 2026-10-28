-- Prove2me | solution 1 for ArbEcon.Off.em_remainder_region
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:15:28.082671+00:00
-- url     : https://prove2.me/submissions/2d245b15-75ec-417d-b12a-2d131a86c05e

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
import Theorems.Thm_ZetaReflection_EMOff_em_zeta_orderK_enclosure_odd_ext
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/





lemma poch_succ (s : ℂ) (k : ℕ) : poch s (k + 1) = poch s k * (s + k) := rfl

lemma norm_poch_succ (s : ℂ) (k : ℕ) : ‖poch s (k + 1)‖ = ‖poch s k‖ * ‖s + k‖ := by
  rw [poch_succ, norm_mul]











/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/



theorem norm_poch_sq (σ t : ℝ) (k : ℕ) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ^ 2 = pochNormSq σ t k := by
  induction k with
  | zero => simp [pochNormSq, poch]
  | succ k ih =>
    rw [norm_poch_succ, mul_pow, ih, pochNormSq, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.natCast_re, Complex.add_im, Complex.mul_im, Complex.natCast_im]
    ring

theorem norm_poch_le (σ t : ℝ) (k : ℕ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : pochNormSq σ t k ≤ Q ^ 2) :
    ‖poch ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ Q := by
  rw [← norm_poch_sq] at hQ
  have h0 := norm_nonneg (poch ((σ : ℂ) + (t : ℂ) * I) k)
  nlinarith [hQ]





/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/













/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/






















end EMHigh

end ZetaReflection


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







/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/





/-! ## T5. The Taylor model of the finite part. -/









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/



theorem CK_nonneg (K : ℕ) : 0 ≤ CK K := by
  unfold CK
  have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
  positivity



theorem pochNormSq_mono (σ t σ' t' : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ σ') (ht : |t| ≤ t') :
    ∀ k : ℕ, pochNormSq σ t k ≤ pochNormSq σ' t' k := by
  intro k
  induction k with
  | zero => simp [pochNormSq]
  | succ k ih =>
    simp only [pochNormSq]
    have h0 : 0 ≤ pochNormSq σ t k := by
      clear ih
      induction k with
      | zero => simp [pochNormSq]
      | succ k ih2 => simp only [pochNormSq]; exact mul_nonneg ih2 (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsq : (σ + k) ^ 2 + t ^ 2 ≤ (σ' + k) ^ 2 + t' ^ 2 := by
      have h1 : (σ + k) ^ 2 ≤ (σ' + k) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 : t ^ 2 ≤ t' ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      linarith
    exact mul_le_mul ih hsq (by positivity) (le_trans h0 ih)



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









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/










theorem solution (K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) (s : ℂ) (hs0 : 1 / 2 ≤ s.re)
    (hs1 : s.re ≤ 1) (hsim : 0 < s.im) (B : ℝ) (hsB : s.im ≤ B) (Qr : ℝ) (hQr0 : 0 ≤ Qr)
    (hQ : pochNormSq 1 B (2 * K + 1) ≤ Qr ^ 2) (r0 : ℕ) (hr0 : 0 < r0) (hr0N : r0 ^ 2 ≤ N) :
    ‖riemannZeta s - emFinite K s N‖
      ≤ CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr0R : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at hsim; simp at hsim
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := s)
    (by push_cast; linarith) hs1' hN
  refine le_trans henc ?_
  -- the Pochhammer factor
  have hseq : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I := (Complex.re_add_im s).symm
  have hmono := pochNormSq_mono s.re s.im 1 B (by linarith) hs1
    (by rw [abs_of_pos hsim]; exact hsB) (2 * K + 1)
  have hpoch : ‖poch s (2 * K + 1)‖ ≤ Qr := by
    rw [hseq]; exact norm_poch_le s.re s.im (2 * K + 1) Qr hQr0 (le_trans hmono hQ)
  -- the power of N
  have hpow : (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ 1 / ((N : ℝ) ^ (2 * K) * r0) := by
    have hsq : (r0 : ℝ) ≤ Real.sqrt N := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact_mod_cast hr0N
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have e : (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ))) = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := by
      rw [Real.rpow_neg hNR.le, Real.rpow_add hNR, Real.rpow_natCast, ← Real.sqrt_eq_rpow, one_div]
      ring
    calc (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
        ≤ (N : ℝ) ^ (-((1 / 2 : ℝ) + ((2 * K : ℕ) : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          push_cast; linarith
      _ = 1 / ((N : ℝ) ^ (2 * K) * Real.sqrt N) := e
      _ ≤ 1 / ((N : ℝ) ^ (2 * K) * r0) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hden : ((2 * K : ℕ) : ℝ) + 1 / 2 ≤ s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hden0 : (0 : ℝ) < ((2 * K : ℕ) : ℝ) + 1 / 2 := by positivity
  have hpn0 : 0 ≤ (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) := by positivity
  have hCK := CK_nonneg K
  change CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
      / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ _
  calc CK K * ‖poch s (2 * K + 1)‖ * (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
        / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)
      ≤ CK K * Qr * (1 / ((N : ℝ) ^ (2 * K) * r0)) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by
        gcongr
    _ = CK K * Qr / ((N : ℝ) ^ (2 * K) * r0) / (((2 * K : ℕ) : ℝ) + 1 / 2) := by ring
