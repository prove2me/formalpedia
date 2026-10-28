-- Prove2me | solution 1 for ArbEcon.Off.remOddG_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:15:08.545431+00:00
-- url     : https://prove2.me/submissions/957ed843-f63d-4b95-af87-78e8cf9d6bda

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
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
import Theorems.Thm_ArbEcon_Off_rpow_neg_le_of_pow
import Theorems.Thm_ZetaReflection_EMOff_em_zeta_orderK_enclosure_odd_ext
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
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


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/



theorem pochNormSq_eq_pnG (sN : ℤ) (q u tn : ℕ) (hq : 0 < q) (hu : 0 < u) (σ t : ℝ)
    (hσ : σ = (sN : ℝ) / q) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    pochNormSq σ t k = (pnG sN q u tn k : ℝ) / ((q : ℝ) * u) ^ (2 * k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochNormSq, pnG]
  | succ k ih =>
    rw [pochNormSq, ih, pnG]
    push_cast
    subst hσ ht
    have hne : ((q : ℝ) * u) ^ (2 * k) ≠ 0 := by positivity
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    field_simp



/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/











end Off

end ArbEcon


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
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

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/



theorem solution (K N : ℕ) (hN : 1 ≤ N) (a b q u tn : ℕ) (hq : 0 < q) (hu : 0 < u)
    (htn : 0 < tn) (σ t : ℝ) (hσ : σ = ((a : ℝ) - b) / q) (ht : t = (tn : ℝ) / u) (Qp Rn Rd : ℕ)
    (hok : (remOddG K a b q u tn N Qp Rn Rd).1 = true) :
    ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖
      ≤ ((remOddG K a b q u tn N Qp Rn Rd).2.1 : ℝ) / ((remOddG K a b q u tn N Qp Rn Rd).2.2 : ℝ) := by
  simp only [remOddG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨⟨hRd, hK⟩, hQ⟩, hR⟩, hpos⟩ := hok
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have htR : 0 < t := by rw [ht]; exact div_pos (by exact_mod_cast htn) huR
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRdR : (0 : ℝ) < Rd := by exact_mod_cast hRd
  set sN : ℤ := (a : ℤ) - b with hsN
  have hσ' : σ = (sN : ℝ) / q := by rw [hσ, hsN]; push_cast; ring
  have hposR : (0 : ℝ) < (sN : ℝ) + 2 * K * q := by exact_mod_cast hpos
  have hσK : 0 < σ + 2 * K := by
    rw [hσ']
    have : (sN : ℝ) / q + 2 * K = ((sN : ℝ) + 2 * K * q) / q := by field_simp
    rw [this]; positivity
  -- the analytic bound
  have hs1 : sOfG σ t ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [sOfG] at this
    linarith
  have hsre : (sOfG σ t).re = σ := by simp [sOfG]
  have henc := EMOff.em_zeta_orderK_enclosure_odd_ext K hK (s := sOfG σ t)
    (by rw [hsre]; push_cast; linarith) hs1 hN
  rw [hsre] at henc
  -- the Pochhammer factor
  set Qr : ℝ := (Qp : ℝ) / ((q : ℝ) * u) ^ (2 * K + 1) with hQr
  have hQr0 : 0 ≤ Qr := by positivity
  have hpn := pochNormSq_eq_pnG sN q u tn hq hu σ t hσ' ht (2 * K + 1)
  have hQsq : pochNormSq σ t (2 * K + 1) ≤ Qr ^ 2 := by
    rw [hpn, hQr, div_pow, ← pow_mul]
    have h2 : (0 : ℝ) < ((q : ℝ) * u) ^ ((2 * K + 1) * 2) := by positivity
    rw [show 2 * (2 * K + 1) = (2 * K + 1) * 2 by ring]
    apply div_le_div_of_nonneg_right _ h2.le
    have : (pnG sN q u tn (2 * K + 1) : ℝ) ≤ ((Qp : ℤ) * Qp : ℤ) := by exact_mod_cast hQ
    push_cast at this; nlinarith [this]
  have hpoch : ‖poch (sOfG σ t) (2 * K + 1)‖ ≤ Qr := norm_poch_le σ t (2 * K + 1) Qr hQr0 hQsq
  -- the power of N
  have hNσ : (N : ℝ) ^ (-σ) ≤ (Rn : ℝ) / Rd := by
    rw [hσ]; exact rpow_neg_le_of_pow N hN a b q hq Rn Rd hRd (by exact_mod_cast hR)
  have hpowN : (N : ℝ) ^ (-(σ + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ (Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K) := by
    have e : -(σ + ((2 * K + 1 : ℕ) : ℝ) - 1) = -σ + (-(((2 * K : ℕ) : ℝ))) := by push_cast; ring
    have hk : (N : ℝ) ^ (-(((2 * K : ℕ) : ℝ))) = ((N : ℝ) ^ (2 * K))⁻¹ := by
      rw [Real.rpow_neg hNR.le, Real.rpow_natCast]
    rw [e, Real.rpow_add hNR, hk, div_eq_mul_inv ((Rn : ℝ) / Rd)]
    exact mul_le_mul_of_nonneg_right hNσ (by positivity)
  have hden : σ + ((2 * K + 1 : ℕ) : ℝ) - 1 = ((sN : ℝ) + 2 * K * q) / q := by
    rw [hσ']; push_cast; field_simp; ring
  -- the constant
  have hlo : (6283184 : ℝ) / 1000000 ≤ 2 * π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hhi : π ≤ (3141593 : ℝ) / 1000000 := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpipos : (0 : ℝ) < π := Real.pi_pos
  have hpi2 : π ^ 2 ≤ ((3141593 : ℝ) / 1000000) ^ 2 := pow_le_pow_left₀ hpipos.le hhi 2
  have hC : 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1)
      ≤ 2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) := by
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
    have hnum0 : 0 ≤ 1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) := by
      have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
      positivity
    rw [← div_pow, ← div_pow]
    gcongr
  have hC0 : 0 ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) := by
    have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
    positivity
  refine le_trans henc ?_
  rw [hden]
  have hdpos : (0 : ℝ) < ((sN : ℝ) + 2 * K * q) / q := by positivity
  have hpowN' : (N : ℝ) ^ (-(((sN : ℝ) + 2 * K * q) / q)) ≤ (Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K) := by
    rw [← hden]; exact hpowN
  have hne1 : (sN : ℝ) + 2 * K * q ≠ 0 := hposR.ne'
  have hne2 : ((q : ℝ) * u) ^ (2 * K + 1) ≠ 0 := by positivity
  have hne3 : (N : ℝ) ^ (2 * K) ≠ 0 := by positivity
  have hne4 : (2 : ℝ) ^ (2 * K - 1) ≠ 0 := by positivity
  have hne5 : (Rd : ℝ) ≠ 0 := hRdR.ne'
  have hne6 : (q : ℝ) ≠ 0 := hqR.ne'
  calc _ ≤ 2 * (1 + ((3141593 : ℝ) ^ 2 / 1000000 ^ 2 / 6 - 1) / 2 ^ (2 * K - 1))
          / ((6283184 : ℝ) ^ (2 * K + 1) / 1000000 ^ (2 * K + 1)) * Qr
          * ((Rn : ℝ) / Rd / (N : ℝ) ^ (2 * K)) / (((sN : ℝ) + 2 * K * q) / q) := by
        gcongr
    _ = _ := by
        rw [hQr]
        push_cast
        field_simp
        ring
