-- Prove2me | solution 1 for ArgZetaTwo.argChangeVert_zeta_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:05.66477+00:00
-- url     : https://prove2.me/submissions/6305a9a7-585c-43b8-adb0-589f5a961ea5

import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ArgZetaTwo_re_zeta_two_pos
import Theorems.Thm_DiffractionCore_continuous_logDeriv_zeta_line2
/-  ArgZetaTwo.lean -- brick K6a of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2d, brick K6a).

    THE BINDER IT DISCHARGES.  Conjunct 5 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) is

        hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1,

    the argument change of ζ up the line `Re s = 2` between the band edges.  The emitted bands feed
    it a 1e-12-wide Arb enclosure.  This file proves a GENERIC enclosure, valid for every `T0`,
    `T1` and hence for all 10,379 bands of the h280000 ladder at once:

        argChangeVert riemannZeta 2 T0 T1 ∈ [-249/250, 249/250]         (`hAV2_generic`)

    because `|arg ζ(2 + i t)| ≤ log ζ(2) = log (π²/6) < 0.498` for every real `t`.

    HOW.
      * `argChangeVert_zeta_two_eq`: the argument change IS a difference of principal arguments,
            argChangeVert ζ 2 T0 T1 = arg ζ(2 + i T1) - arg ζ(2 + i T0),
        by the fundamental theorem of calculus for `y ↦ log ζ(2 + i y)` (principal `Complex.log`),
        legitimate because `ζ(2 + i y)` stays in the right half-plane.
      * `arg_zeta_eq_im_primeLog`, `abs_arg_zeta_two_le`: on `Re s = 2`, ζ(s) = exp L(s) with
        L(s) = Σ_p -log(1 - p^{-s}) (Mathlib's `riemannZeta_eulerProduct_exp_log`), and
        ‖L(s)‖ ≤ Σ_p -log(1 - p^{-2}) =: G termwise (Taylor series of `-log(1 - z)` dominated
        by that of `-log(1 - ‖z‖)`).  Since G < π, `Complex.log (exp L) = L`, so
        arg ζ(s) = Im L(s) ∈ [-G, G]; since G < π/2, Re ζ(s) > 0.
      * `exp_primeSum`: exp G = ζ(2) = π²/6 (the same Euler product at the real point 2), so
        G = log (π²/6); `log_pi_sq_div_six_lt`: log (π²/6) < 249/500 from π < 3.1416 and the
        degree-6 Taylor lower bound of `exp`.

    This is the "Λ(n) series at σ = 2" bound of the memo: mathematically G = Σ_n Λ(n)/(n² log n) =
    log ζ(2); the formal route here is the prime Euler product, not the Λ(n) series itself.
    (Not formalized, for orientation only: by Kronecker's theorem the supremum of |arg ζ(2+it)| is
    Σ_p arcsin(p⁻²) ≈ 0.455, so the constant is within 10 percent of optimal.)

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A height-uniform bound on one edge of a finite zero count; nothing
    here bears on the Riemann Hypothesis. -/



open Complex

namespace ArgZetaTwo

/-! ## 1. The logarithm of the Euler product -/











/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/





























/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/













theorem zeta_two_mem_slitPlane (t : ℝ) : riemannZeta ((2 : ℂ) + (t : ℂ) * I) ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_zeta_two_pos t))

/-! ## 4. The argument change up `Re s = 2` -/









end ArgZetaTwo


/-  ArgZetaTwo.lean -- brick K6a of the ANDURIL Arb discharge
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2d, brick K6a).

    THE BINDER IT DISCHARGES.  Conjunct 5 of the `hArbT` binder of every emitted Turing band
    (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) is

        hAV2 : DiffractionCore.argChangeVert riemannZeta 2 T0 T1 ∈ Set.Icc L1 H1,

    the argument change of ζ up the line `Re s = 2` between the band edges.  The emitted bands feed
    it a 1e-12-wide Arb enclosure.  This file proves a GENERIC enclosure, valid for every `T0`,
    `T1` and hence for all 10,379 bands of the h280000 ladder at once:

        argChangeVert riemannZeta 2 T0 T1 ∈ [-249/250, 249/250]         (`hAV2_generic`)

    because `|arg ζ(2 + i t)| ≤ log ζ(2) = log (π²/6) < 0.498` for every real `t`.

    HOW.
      * `argChangeVert_zeta_two_eq`: the argument change IS a difference of principal arguments,
            argChangeVert ζ 2 T0 T1 = arg ζ(2 + i T1) - arg ζ(2 + i T0),
        by the fundamental theorem of calculus for `y ↦ log ζ(2 + i y)` (principal `Complex.log`),
        legitimate because `ζ(2 + i y)` stays in the right half-plane.
      * `arg_zeta_eq_im_primeLog`, `abs_arg_zeta_two_le`: on `Re s = 2`, ζ(s) = exp L(s) with
        L(s) = Σ_p -log(1 - p^{-s}) (Mathlib's `riemannZeta_eulerProduct_exp_log`), and
        ‖L(s)‖ ≤ Σ_p -log(1 - p^{-2}) =: G termwise (Taylor series of `-log(1 - z)` dominated
        by that of `-log(1 - ‖z‖)`).  Since G < π, `Complex.log (exp L) = L`, so
        arg ζ(s) = Im L(s) ∈ [-G, G]; since G < π/2, Re ζ(s) > 0.
      * `exp_primeSum`: exp G = ζ(2) = π²/6 (the same Euler product at the real point 2), so
        G = log (π²/6); `log_pi_sq_div_six_lt`: log (π²/6) < 249/500 from π < 3.1416 and the
        degree-6 Taylor lower bound of `exp`.

    This is the "Λ(n) series at σ = 2" bound of the memo: mathematically G = Σ_n Λ(n)/(n² log n) =
    log ζ(2); the formal route here is the prime Euler product, not the Λ(n) series itself.
    (Not formalized, for orientation only: by Kronecker's theorem the supremum of |arg ζ(2+it)| is
    Σ_p arcsin(p⁻²) ≈ 0.455, so the constant is within 10 percent of optimal.)

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  A height-uniform bound on one edge of a finite zero count; nothing
    here bears on the Riemann Hypothesis. -/



open Complex

section
namespace ArgZetaTwo
end ArgZetaTwo
open ArgZetaTwo

/-! ## 1. The logarithm of the Euler product -/











/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/





























/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/















/-! ## 4. The argument change up `Re s = 2` -/


theorem solution (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert riemannZeta 2 T0 T1
      = Complex.arg (riemannZeta ((2 : ℂ) + (T1 : ℂ) * I))
        - Complex.arg (riemannZeta ((2 : ℂ) + (T0 : ℂ) * I)) := by
  set γ : ℝ → ℂ := fun y => (2 : ℂ) + (y : ℂ) * I with hγdef
  have hγ : ∀ y : ℝ, HasDerivAt γ I y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    have h2 := (h1.mul_const I).const_add (2 : ℂ)
    simpa [hγdef] using h2
  have hne1 : ∀ y : ℝ, γ y ≠ 1 := by
    intro y h
    have := congrArg Complex.re h
    simp [hγdef] at this
  have hζ : ∀ y : ℝ, HasDerivAt (fun y => riemannZeta (γ y)) (deriv riemannZeta (γ y) * I) y :=
    fun y => ((differentiableAt_riemannZeta (hne1 y)).hasDerivAt).comp y (hγ y)
  have hG : ∀ y : ℝ, HasDerivAt (fun y => Complex.log (riemannZeta (γ y)))
      (deriv riemannZeta (γ y) * I / riemannZeta (γ y)) y :=
    fun y => (hζ y).clog_real (zeta_two_mem_slitPlane y)
  have heq : (fun y => deriv riemannZeta (γ y) * I / riemannZeta (γ y))
      = fun y => I * logDeriv riemannZeta (γ y) := by
    funext y; rw [logDeriv_apply]; ring
  have hcont : Continuous (fun y : ℝ => I * logDeriv riemannZeta (γ y)) :=
    continuous_const.mul DiffractionCore.continuous_logDeriv_zeta_line2
  have hint : IntervalIntegrable (fun y => deriv riemannZeta (γ y) * I / riemannZeta (γ y))
      MeasureTheory.volume T0 T1 := by
    rw [heq]; exact hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hG y) hint
  rw [heq, intervalIntegral.integral_const_mul] at hFTC
  have him := congrArg Complex.im hFTC
  rw [Complex.sub_im, Complex.log_im, Complex.log_im] at him
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at him
  unfold DiffractionCore.argChangeVert
  rw [show (((2 : ℝ)) : ℂ) = (2 : ℂ) by norm_num]
  exact him
