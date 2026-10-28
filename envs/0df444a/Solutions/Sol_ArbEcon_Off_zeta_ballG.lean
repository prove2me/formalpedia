-- Prove2me | solution 1 for ArbEcon.Off.zeta_ballG
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:04.58963+00:00
-- url     : https://prove2.me/submissions/c40b406a-2458-4f05-9470-c9917fe379da

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
import Theorems.Thm_ZetaReflection_EMHigh_emCorr_re_im
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

namespace ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/









theorem two_pow_pos' (P : ℕ) : (0 : ℝ) < (2 : ℝ) ^ P := by positivity

/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/























end ArbEcon


/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/

theorem psumK_succ (σ t : ℝ) (k n : ℕ) :
    psumK σ t k (n + 1) = psumK σ t k n
      + ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-sOfG σ t) := by
  simp only [psumK]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]





/-! ## G. One step, the run, the chunks. -/

















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

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/

theorem psumK_zero_eq (σ t : ℝ) (n : ℕ) :
    psumK σ t 0 n = ∑ m ∈ Finset.Ico 1 (n + 1), (m : ℂ) ^ (-sOfG σ t) := by
  simp [psumK]

theorem emFinite_split (K : ℕ) (σ t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    emFinite K (sOfG σ t) N
      = psumK σ t 0 (N - 1) + (N : ℂ) ^ (-sOfG σ t) * emCorr K (sOfG σ t) N := by
  rw [psumK_zero_eq, show N - 1 + 1 = N by omega]
  rfl



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





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/





theorem solution (P : ℕ) (σ t : ℝ) (K N : ℕ) (hN : 2 ≤ N) (x1 x2 : Acc)
    (h1 : AccOK P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK P (psumK σ t 0 N) x2) (E : ℝ)
    (hE : ‖riemannZeta (sOfG σ t) - emFinite K (sOfG σ t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K σ t N = Bre) (hBim : emCorrIm K σ t N = Bim) :
    let a1 := (x1.reP : ℝ) - x1.reN
    let b1 := (x1.imP : ℝ) - x1.imN
    let za := ((x2.reP : ℝ) - x2.reN) - a1
    let zb := ((x2.imP : ℝ) - x2.imN) - b1
    let zra := (x2.reR : ℝ) + x1.reR
    let zrb := (x2.imR : ℝ) + x1.imR
    |(riemannZeta (sOfG σ t)).re * 2 ^ P - (a1 + za * Bre - zb * Bim)|
        ≤ x1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ P ∧
    |(riemannZeta (sOfG σ t)).im * 2 ^ P - (b1 + za * Bim + zb * Bre)|
        ≤ x1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ P := by
  intro a1 b1 za zb zra zrb
  obtain ⟨hre1, him1⟩ := h1
  obtain ⟨hre2, him2⟩ := h2
  have hP : (0 : ℝ) < 2 ^ P := two_pow_pos' P
  have hNm : N - 1 + 1 = N := by omega
  have hZ : (N : ℂ) ^ (-sOfG σ t) = psumK σ t 0 N - psumK σ t 0 (N - 1) := by
    have := psumK_succ σ t 0 (N - 1)
    rw [hNm] at this
    rw [this, pow_zero, one_mul]; ring
  have hZre : |((N : ℂ) ^ (-sOfG σ t)).re * 2 ^ P - za| ≤ zra := by
    rw [hZ, Complex.sub_re]
    have : ((psumK σ t 0 N).re - (psumK σ t 0 (N - 1)).re) * 2 ^ P - za
        = ((psumK σ t 0 N).re * 2 ^ P - ((x2.reP : ℝ) - x2.reN))
          - ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hZim : |((N : ℂ) ^ (-sOfG σ t)).im * 2 ^ P - zb| ≤ zrb := by
    rw [hZ, Complex.sub_im]
    have : ((psumK σ t 0 N).im - (psumK σ t 0 (N - 1)).im) * 2 ^ P - zb
        = ((psumK σ t 0 N).im * 2 ^ P - ((x2.imP : ℝ) - x2.imN))
          - ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  have hsplit := emFinite_split K σ t N (by omega)
  set B := emCorr K (sOfG σ t) N with hB
  have hBre' : B.re = Bre := by rw [← hBre]; exact (emCorr_re_im K σ t N).1
  have hBim' : B.im = Bim := by rw [← hBim]; exact (emCorr_re_im K σ t N).2
  set Z := (N : ℂ) ^ (-sOfG σ t)
  have hEre : |(riemannZeta (sOfG σ t)).re - (emFinite K (sOfG σ t) N).re| ≤ E := by
    rw [← Complex.sub_re]; exact le_trans (Complex.abs_re_le_norm _) hE
  have hEim : |(riemannZeta (sOfG σ t)).im - (emFinite K (sOfG σ t) N).im| ≤ E := by
    rw [← Complex.sub_im]; exact le_trans (Complex.abs_im_le_norm _) hE
  rw [hsplit] at hEre hEim
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hBre', hBim']
    at hEre hEim
  constructor
  · have e : (riemannZeta (sOfG σ t)).re * 2 ^ P - (a1 + za * Bre - zb * Bim)
        = ((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ P
          + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
          + (Z.re * 2 ^ P - za) * Bre - (Z.im * 2 ^ P - zb) * Bim := by ring
    rw [e]
    have t1 : |((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
        * 2 ^ P| ≤ E * 2 ^ P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEre (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ P - za) * Bre| ≤ zra * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ P - zb) * Bim| ≤ zrb * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1))
      ((Z.re * 2 ^ P - za) * Bre)
    have q2 := abs_add_le (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P) ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
    have q3 := abs_sub (((riemannZeta (sOfG σ t)).re - ((psumK σ t 0 (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ P + ((psumK σ t 0 (N - 1)).re * 2 ^ P - a1)
      + (Z.re * 2 ^ P - za) * Bre) ((Z.im * 2 ^ P - zb) * Bim)
    linarith
  · have e : (riemannZeta (sOfG σ t)).im * 2 ^ P - (b1 + za * Bim + zb * Bre)
        = ((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ P
          + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
          + (Z.re * 2 ^ P - za) * Bim + (Z.im * 2 ^ P - zb) * Bre := by ring
    rw [e]
    have t1 : |((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
        * 2 ^ P| ≤ E * 2 ^ P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEim (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ P - za) * Bim| ≤ zra * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ P - zb) * Bre| ≤ zrb * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1))
      ((Z.re * 2 ^ P - za) * Bim)
    have q2 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P) ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
    have q3 := abs_add_le (((riemannZeta (sOfG σ t)).im - ((psumK σ t 0 (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ P + ((psumK σ t 0 (N - 1)).im * 2 ^ P - b1)
      + (Z.re * 2 ^ P - za) * Bim) ((Z.im * 2 ^ P - zb) * Bre)
    linarith
