-- Prove2me | solution 1 for ArbEcon.Off.slabClear_of_right_half
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:48:43.364084+00:00
-- url     : https://prove2.me/submissions/bb73dce2-4bfd-4c7f-8df2-1b0ea19cc857

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
/- PHASE 4 (dVP frontier / RH-in-a-box, piece 3 — functional-equation symmetry): halve the work.

   For the "all nontrivial zeros up to height `T` lie on the critical line" certificate, the
   functional equation `ζ(1-s) = 2·(2π)^{-s}·Γ(s)·cos(πs/2)·ζ(s)` (`riemannZeta_one_sub`) reflects
   zeros across `Re = 1/2`: if `ζ ρ = 0` then `ζ (1-ρ) = 0`, and `1-ρ` has real part `1 - Re ρ`
   (reflected about `1/2`) and imaginary part `-Im ρ` (so `|Im|` is unchanged).

   Hence it SUFFICES to clear the right half of the critical strip: if there are no zeros with
   `1/2 < Re < 1` and `|Im| ≤ T`, then every strip zero with `|Im| ≤ T` lies on `Re = 1/2`.  This
   halves the region the box-driver must certify.  Self-contained: only `riemannZeta_one_sub`.

   conjecture1_proved = False (NOT a proof of RH — a symmetry reduction, not an exclusion of zeros).
-/


open Complex

namespace ZeroFreeBridge

/-- **Functional-equation reflection of a ζ-zero across `Re = 1/2`.**  A zero `ρ` in the open
    critical strip (`0 < Re ρ < 1`) reflects to a zero at `1 - ρ` (`riemannZeta_one_sub`, the
    factor is finite so it kills `ζ ρ = 0`). -/
theorem riemannZeta_one_sub_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 - ρ) = 0 := by
  have hn : ∀ n : ℕ, ρ ≠ -n := by
    intro n h; rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  rw [riemannZeta_one_sub hn hne1, hz, mul_zero]



/-- **Conjugation reflection of a ζ-zero across the real axis.**  `ζ ρ = 0 ⟹ ζ (conj ρ) = 0`
    (`riemannZeta_conj`, `conj 0 = 0`). -/
theorem riemannZeta_conj_eq_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    riemannZeta ((starRingEnd ℂ) ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]



/-- **Width-fold reflection across the critical line, PRESERVING the imaginary part.**  Composing
    the functional equation (`riemannZeta_one_sub_eq_zero`, `ρ ↦ 1 - ρ`) with conjugation
    (`riemannZeta_conj_eq_zero`, `ρ ↦ conj ρ`) yields the reflection `ρ ↦ 1 - conj ρ` across the
    vertical line `Re = 1/2` that keeps `Im` fixed: a zero at `β + iγ` (`0 < β < 1`) maps to a zero
    at `(1 - β) + iγ`.  This is the symmetry that folds a fixed-`Im`-band box `[a, 1-a] × [T0,T1]`
    onto its left half `[a, 1/2] × [T0,T1]` (unlike `riemannZeta_one_sub_eq_zero`, which flips the
    sign of `Im` and so leaves a single `Im`-band). -/
theorem riemannZeta_reflect_line_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 - (starRingEnd ℂ) ρ) = 0 := by
  have hc : riemannZeta ((starRingEnd ℂ) ρ) = 0 := riemannZeta_conj_eq_zero hz
  have h0' : 0 < ((starRingEnd ℂ) ρ).re := by rw [Complex.conj_re]; exact h0
  have h1' : ((starRingEnd ℂ) ρ).re < 1 := by rw [Complex.conj_re]; exact h1
  exact riemannZeta_one_sub_eq_zero h0' h1' hc

end ZeroFreeBridge




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








theorem solution (a b : ℝ)
    (hR : ∀ x y : ℝ, 1 / 2 ≤ x → x < 1 → a ≤ y → y ≤ b → riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    EdgeClearGlue.SlabClear a b := by
  intro x y hx0 hx1 hya hyb hz
  by_cases hh : 1 / 2 ≤ x
  · exact hR x y hh hx1 hya hyb hz
  · push Not at hh
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    have hz' := ZeroFreeBridge.riemannZeta_reflect_line_eq_zero (ρ := (x : ℂ) + (y : ℂ) * I)
      (by rw [hre]; exact hx0) (by rw [hre]; exact hx1) hz
    have e : 1 - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * I) = ((1 - x : ℝ) : ℂ) + (y : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e] at hz'
    exact hR (1 - x) y (by linarith) (by linarith) hya hyb hz'
