-- Prove2me | solution 1 for ArbEcon.Off.dist_le_of_box
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:24.291996+00:00
-- url     : https://prove2.me/submissions/344127f4-cdd9-4ef4-bb9f-da8e34d8ab82

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
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

/-  EMZetaOfflineSlabClear.lean -- lane offline: from kernel-checked cells to an edge-clearance slab
    `EdgeClearGlue.SlabClear a b` (brick K1's numerical input, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    rows H2a/H2c).

      * `cell_zeta_ne_zero` -- ONE cell, packaged: two evaluator invariants at the center
                               `c = σc + i tc` (after `N - 1` and `N` terms, `p + 1` accumulators), the
                               kernel check `checkCell … = true`, and a handful of scalar side
                               conditions (log bracket, `r L ≤ 1`, `‖c + j‖ ≤ U`, the remainder
                               certificate, the error budget) give `ζ(s) ≠ 0` for every `s` with
                               `‖s - c‖ ≤ r`, `a ≤ Im s ≤ B`, `1/2 ≤ Re s ≤ 1`;
      * `slabClear_of_right_half` -- the reflection `ρ ↦ 1 - conj ρ` (Im-preserving) folds
                               `0 < Re < 1/2` onto `1/2 < Re < 1`, so the right half of a slab suffices.

    conjecture1_proved = False.  A finite, local nonvanishing statement; nothing about RH.
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










theorem solution (x y σc tc w hh r : ℝ) (hx : |x - σc| ≤ w) (hy : |y - tc| ≤ hh)
    (hr0 : 0 ≤ r) (hr : w ^ 2 + hh ^ 2 ≤ r ^ 2) :
    ‖((x : ℂ) + (y : ℂ) * I) - sOfG σc tc‖ ≤ r := by
  have e : ((x : ℂ) + (y : ℂ) * I) - sOfG σc tc = ((x - σc : ℝ) : ℂ) + ((y - tc : ℝ) : ℂ) * I := by
    simp only [sOfG]; push_cast; ring
  rw [e]
  have hsq : ‖((x - σc : ℝ) : ℂ) + ((y - tc : ℝ) : ℂ) * I‖ ^ 2 ≤ r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have h1 : (x - σc) ^ 2 ≤ w ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    have h2 : (y - tc) ^ 2 ≤ hh ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) hr0 hsq
