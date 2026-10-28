-- Prove2me | solution 1 for ArbEcon.OrderK.zeta_ballK
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:09.762985+00:00
-- url     : https://prove2.me/submissions/8e2ac454-f3bd-4f6d-84a5-9609693f2cfc

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
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


/-  Probes/ArbEconomics_Zeta.lean -- from the evaluator invariant to kernel-checked enclosures of
    Re / Im zeta(1/2 + i t).

    Chain (all proved here, no numeric hypotheses):
      * `emZetaFinite3_split` : `emZetaFinite3 s N = psum t (N-1) + N^(-s) * B(t, N)` with
        `B = N/(s-1) + 1/2 + s/(12 N)` (from `ZetaEMSum.emZetaFinite3_eq_dirichlet`);
      * `B_re`, `B_im`       : closed real forms of `B`;
      * `em3_remainder_le`   : the island's order-3 Euler-Maclaurin remainder
        (`EMZetaTail.em_zeta_critical_line3_enclosure`) bounded by `Q / (180 N^2 r)` for rational
        `Q >= |s(s+1)(s+2)|` and `r <= sqrt N`;
      * `zeta_ball`          : two evaluator invariants (after `N-1` and `N` terms) plus the
        remainder bound give explicit balls for `Re zeta` and `Im zeta`.
    An instance then needs only kernel-checked chunks and one `norm_num` on rationals.

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Complex ZetaReflection

namespace ArbEcon






theorem psum_succ (t : ℝ) (n : ℕ) :
    psum t (n + 1) = psum t n + ((n + 1 : ℕ) : ℂ) ^ (-sOf t) := by
  simp only [psum]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
  rfl















end ArbEcon


/-  EMZetaHighEval.lean -- the order-(2K+1) Euler-Maclaurin enclosure of ζ on the critical line,
    wired to the Nat-only kernel evaluator of the ArbEconomics seat (lane emhigh).

    Chain (all proved here, no numeric hypotheses):
      * `emFinite_line_split` : `emFinite K (1/2+it) N = psum t (N-1) + N^(-s) · emCorr K s N`;
      * `emCorr_line_re_im`   : `Re/Im emCorr K s N = emCorrRe/emCorrIm K (1/2) t N`
                                (closed real forms, `EMZetaHigh.emCorr_re_im`);
      * `zeta_ballK`          : two evaluator invariants (after `N-1` and `N` terms, from
                                `ArbEcon.chunk_sound`) plus ANY remainder bound `E` of the
                                order-(2K+1) finite part give explicit balls for Re ζ and Im ζ;
      * `zetaK_re_bounds` / `zetaK_im_bounds` : final forms `lo ≤ Re/Im ζ(1/2+it) ≤ hi` from rational
                                side conditions (checked per instance by `norm_num`).
    The remainder `E` comes from `EMZetaHigh.em_line_remainder_le` (general K, proved).

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh

namespace ArbEcon

namespace OrderK

theorem sOf_eq (t : ℝ) : sOf t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  simp only [sOf]; push_cast; ring

/-- The Dirichlet split of the order-(2K+1) finite part on the critical line. -/
theorem emFinite_line_split (K : ℕ) (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    emFinite K (sOf t) N = psum t (N - 1) + (N : ℂ) ^ (-sOf t) * emCorr K (sOf t) N := by
  simp only [emFinite, psum]
  rw [show N - 1 + 1 = N by omega]
  rfl

theorem emCorr_line_re_im (K : ℕ) (t : ℝ) (N : ℕ) :
    (emCorr K (sOf t) N).re = emCorrRe K (1 / 2) t N ∧
    (emCorr K (sOf t) N).im = emCorrIm K (1 / 2) t N := by
  rw [sOf_eq]; exact emCorr_re_im K (1 / 2) t N







end OrderK

end ArbEcon


/-  EMZetaHighEval.lean -- the order-(2K+1) Euler-Maclaurin enclosure of ζ on the critical line,
    wired to the Nat-only kernel evaluator of the ArbEconomics seat (lane emhigh).

    Chain (all proved here, no numeric hypotheses):
      * `emFinite_line_split` : `emFinite K (1/2+it) N = psum t (N-1) + N^(-s) · emCorr K s N`;
      * `emCorr_line_re_im`   : `Re/Im emCorr K s N = emCorrRe/emCorrIm K (1/2) t N`
                                (closed real forms, `EMZetaHigh.emCorr_re_im`);
      * `zeta_ballK`          : two evaluator invariants (after `N-1` and `N` terms, from
                                `ArbEcon.chunk_sound`) plus ANY remainder bound `E` of the
                                order-(2K+1) finite part give explicit balls for Re ζ and Im ζ;
      * `zetaK_re_bounds` / `zetaK_im_bounds` : final forms `lo ≤ Re/Im ζ(1/2+it) ≤ hi` from rational
                                side conditions (checked per instance by `norm_num`).
    The remainder `E` comes from `EMZetaHigh.em_line_remainder_le` (general K, proved).

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.OrderK
end ArbEcon.OrderK
open ArbEcon.OrderK








theorem solution (c : Cfg) (K : ℕ) (t : ℝ) (N : ℕ) (hN : 2 ≤ N) (s1 s2 : St)
    (h1 : Inv c t (N - 1) s1) (h2 : Inv c t N s2) (E : ℝ)
    (hE : ‖riemannZeta (sOf t) - emFinite K (sOf t) N‖ ≤ E) (Bre Bim : ℝ)
    (hBre : emCorrRe K (1 / 2) t N = Bre) (hBim : emCorrIm K (1 / 2) t N = Bim) :
    let a1 := (s1.reP : ℝ) - s1.reN
    let b1 := (s1.imP : ℝ) - s1.imN
    let za := ((s2.reP : ℝ) - s2.reN) - a1
    let zb := ((s2.imP : ℝ) - s2.imN) - b1
    let zra := (s2.reR : ℝ) + s1.reR
    let zrb := (s2.imR : ℝ) + s1.imR
    |(riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)|
        ≤ s1.reR + zra * |Bre| + zrb * |Bim| + E * 2 ^ c.P ∧
    |(riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)|
        ≤ s1.imR + zra * |Bim| + zrb * |Bre| + E * 2 ^ c.P := by
  intro a1 b1 za zb zra zrb
  obtain ⟨_, _, _, _, hre1, him1⟩ := h1
  obtain ⟨_, _, _, _, hre2, him2⟩ := h2
  have hP : (0 : ℝ) < 2 ^ c.P := two_pow_pos' c.P
  have hNm : N - 1 + 1 = N := by omega
  have hZ : (N : ℂ) ^ (-sOf t) = psum t N - psum t (N - 1) := by
    have := psum_succ t (N - 1); rw [hNm] at this; rw [this]; ring
  have hZre : |((N : ℂ) ^ (-sOf t)).re * 2 ^ c.P - za| ≤ zra := by
    rw [hZ, Complex.sub_re]
    have : ((psum t N).re - (psum t (N - 1)).re) * 2 ^ c.P - za
        = ((psum t N).re * 2 ^ c.P - ((s2.reP : ℝ) - s2.reN))
          - ((psum t (N - 1)).re * 2 ^ c.P - a1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hZim : |((N : ℂ) ^ (-sOf t)).im * 2 ^ c.P - zb| ≤ zrb := by
    rw [hZ, Complex.sub_im]
    have : ((psum t N).im - (psum t (N - 1)).im) * 2 ^ c.P - zb
        = ((psum t N).im * 2 ^ c.P - ((s2.imP : ℝ) - s2.imN))
          - ((psum t (N - 1)).im * 2 ^ c.P - b1) := by ring
    rw [this]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  have hsplit := emFinite_line_split K t N (by omega)
  set B := emCorr K (sOf t) N with hB
  have hBre' : B.re = Bre := by rw [(emCorr_line_re_im K t N).1, hBre]
  have hBim' : B.im = Bim := by rw [(emCorr_line_re_im K t N).2, hBim]
  set Z := (N : ℂ) ^ (-sOf t)
  have hEre : |(riemannZeta (sOf t)).re - (emFinite K (sOf t) N).re| ≤ E := by
    rw [← Complex.sub_re]; exact le_trans (Complex.abs_re_le_norm _) hE
  have hEim : |(riemannZeta (sOf t)).im - (emFinite K (sOf t) N).im| ≤ E := by
    rw [← Complex.sub_im]; exact le_trans (Complex.abs_im_le_norm _) hE
  rw [hsplit] at hEre hEim
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, hBre', hBim']
    at hEre hEim
  constructor
  · have e : (riemannZeta (sOf t)).re * 2 ^ c.P - (a1 + za * Bre - zb * Bim)
        = ((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P
          + ((psum t (N - 1)).re * 2 ^ c.P - a1)
          + (Z.re * 2 ^ c.P - za) * Bre - (Z.im * 2 ^ c.P - zb) * Bim := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).re - ((psum t (N - 1)).re + (Z.re * Bre - Z.im * Bim)))
        * 2 ^ c.P| ≤ E * 2 ^ c.P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEre (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bre| ≤ zra * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bim| ≤ zrb * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P + ((psum t (N - 1)).re * 2 ^ c.P - a1))
      ((Z.re * 2 ^ c.P - za) * Bre)
    have q2 := abs_add_le (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P) ((psum t (N - 1)).re * 2 ^ c.P - a1)
    have q3 := abs_sub (((riemannZeta (sOf t)).re - ((psum t (N - 1)).re
      + (Z.re * Bre - Z.im * Bim))) * 2 ^ c.P + ((psum t (N - 1)).re * 2 ^ c.P - a1)
      + (Z.re * 2 ^ c.P - za) * Bre) ((Z.im * 2 ^ c.P - zb) * Bim)
    linarith
  · have e : (riemannZeta (sOf t)).im * 2 ^ c.P - (b1 + za * Bim + zb * Bre)
        = ((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P
          + ((psum t (N - 1)).im * 2 ^ c.P - b1)
          + (Z.re * 2 ^ c.P - za) * Bim + (Z.im * 2 ^ c.P - zb) * Bre := by ring
    rw [e]
    have t1 : |((riemannZeta (sOf t)).im - ((psum t (N - 1)).im + (Z.re * Bim + Z.im * Bre)))
        * 2 ^ c.P| ≤ E * 2 ^ c.P := by
      rw [abs_mul, abs_of_pos hP]; exact mul_le_mul_of_nonneg_right hEim (le_of_lt hP)
    have t3 : |(Z.re * 2 ^ c.P - za) * Bim| ≤ zra * |Bim| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZre (abs_nonneg _)
    have t4 : |(Z.im * 2 ^ c.P - zb) * Bre| ≤ zrb * |Bre| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hZim (abs_nonneg _)
    have q1 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P + ((psum t (N - 1)).im * 2 ^ c.P - b1))
      ((Z.re * 2 ^ c.P - za) * Bim)
    have q2 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P) ((psum t (N - 1)).im * 2 ^ c.P - b1)
    have q3 := abs_add_le (((riemannZeta (sOf t)).im - ((psum t (N - 1)).im
      + (Z.re * Bim + Z.im * Bre))) * 2 ^ c.P + ((psum t (N - 1)).im * 2 ^ c.P - b1)
      + (Z.re * 2 ^ c.P - za) * Bim) ((Z.im * 2 ^ c.P - zb) * Bre)
    linarith
