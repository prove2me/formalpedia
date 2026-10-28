-- Prove2me | solution 1 for ArbEcon.Off.wball_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:30.910857+00:00
-- url     : https://prove2.me/submissions/6d67aab0-b411-4497-b018-b3e16cffe512

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
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
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh

/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
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

/-! ## A. The Taylor weights from the evaluator's partial sums. -/



/-! ## B. The ball of a weight. -/





theorem solution (P : ℕ) (A1 A2 : ℂ) (x1 x2 : Acc) (h1 : AccOK P A1 x1) (h2 : AccOK P A2 x2)
    (BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD) (B : ℂ) (hBre : B.re = (BreN : ℝ) / BD)
    (hBim : B.im = (BimN : ℝ) / BD) :
    |(A1 + (A2 - A1) * B).re * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.1 : ℝ) ∧
    |(A1 + (A2 - A1) * B).im * 2 ^ P * BD - ((wData BreN BimN BD x1 x2).2.1 : ℝ)|
        ≤ ((wData BreN BimN BD x1 x2).2.2.2 : ℝ) := by
  obtain ⟨hre1, him1⟩ := h1
  obtain ⟨hre2, him2⟩ := h2
  have hBDne : (BD : ℝ) ≠ 0 := ne_of_gt hBD
  simp only [wData]
  push_cast
  have hzre : |(A2 - A1).re * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)))|
      ≤ (x2.reR : ℝ) + x1.reR := by
    rw [Complex.sub_re]
    have e : (A2.re - A1.re) * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN)))
        = (A2.re * 2 ^ P - ((x2.reP : ℝ) - x2.reN)) - (A1.re * 2 ^ P - ((x1.reP : ℝ) - x1.reN)) := by ring
    rw [e]; exact le_trans (abs_sub _ _) (add_le_add hre2 hre1)
  have hzim : |(A2 - A1).im * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)))|
      ≤ (x2.imR : ℝ) + x1.imR := by
    rw [Complex.sub_im]
    have e : (A2.im - A1.im) * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN)))
        = (A2.im * 2 ^ P - ((x2.imP : ℝ) - x2.imN)) - (A1.im * 2 ^ P - ((x1.imP : ℝ) - x1.imN)) := by ring
    rw [e]; exact le_trans (abs_sub _ _) (add_le_add him2 him1)
  set u1 := A1.re * 2 ^ P - ((x1.reP : ℝ) - x1.reN) with hu1
  set v1 := A1.im * 2 ^ P - ((x1.imP : ℝ) - x1.imN) with hv1
  set ua := (A2 - A1).re * 2 ^ P - ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) with hua
  set va := (A2 - A1).im * 2 ^ P - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) with hva
  have hWre : (A1 + (A2 - A1) * B).re = A1.re + (A2 - A1).re * B.re - (A2 - A1).im * B.im := by
    simp [Complex.add_re, Complex.mul_re]; ring
  have hWim : (A1 + (A2 - A1) * B).im = A1.im + (A2 - A1).re * B.im + (A2 - A1).im * B.re := by
    simp [Complex.add_im, Complex.mul_im]; ring
  rw [hWre, hWim, hBre, hBim]
  constructor
  · have e : (A1.re + (A2 - A1).re * ((BreN : ℝ) / BD) - (A2 - A1).im * ((BimN : ℝ) / BD)) * 2 ^ P * BD
        - ((((x1.reP : ℝ) - x1.reN) * BD + ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) * BreN
          - ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) * BimN))
        = u1 * BD + ua * BreN - va * BimN := by
      rw [hu1, hua, hva]; field_simp; ring
    rw [e]
    have t1 : |u1 * BD| ≤ x1.reR * BD := by
      rw [abs_mul, abs_of_pos hBD]; exact mul_le_mul_of_nonneg_right hre1 hBD.le
    have t2 : |ua * BreN| ≤ ((x2.reR : ℝ) + x1.reR) * |(BreN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzre (abs_nonneg _)
    have t3 : |va * BimN| ≤ ((x2.imR : ℝ) + x1.imR) * |(BimN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzim (abs_nonneg _)
    have q1 := abs_sub (u1 * BD + ua * BreN) (va * BimN)
    have q2 := abs_add_le (u1 * BD) (ua * BreN)
    linarith
  · have e : (A1.im + (A2 - A1).re * ((BimN : ℝ) / BD) + (A2 - A1).im * ((BreN : ℝ) / BD)) * 2 ^ P * BD
        - ((((x1.imP : ℝ) - x1.imN) * BD + ((((x2.reP : ℝ) - x2.reN) - ((x1.reP : ℝ) - x1.reN))) * BimN
          + ((((x2.imP : ℝ) - x2.imN) - ((x1.imP : ℝ) - x1.imN))) * BreN))
        = v1 * BD + ua * BimN + va * BreN := by
      rw [hv1, hua, hva]; field_simp; ring
    rw [e]
    have t1 : |v1 * BD| ≤ x1.imR * BD := by
      rw [abs_mul, abs_of_pos hBD]; exact mul_le_mul_of_nonneg_right him1 hBD.le
    have t2 : |ua * BimN| ≤ ((x2.reR : ℝ) + x1.reR) * |(BimN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzre (abs_nonneg _)
    have t3 : |va * BreN| ≤ ((x2.imR : ℝ) + x1.imR) * |(BreN : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hzim (abs_nonneg _)
    have q1 := abs_add_le (v1 * BD + ua * BimN) (va * BreN)
    have q2 := abs_add_le (v1 * BD) (ua * BimN)
    linarith
