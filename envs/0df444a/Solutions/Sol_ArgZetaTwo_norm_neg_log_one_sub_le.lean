-- Prove2me | solution 1 for ArgZetaTwo.norm_neg_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:32:04.009835+00:00
-- url     : https://prove2.me/submissions/97b46055-84dc-4763-b6f6-2eac9346c75f

import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib

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






theorem solution {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  have hc := Complex.hasSum_taylorSeries_neg_log hz
  have hr0 : ‖((‖z‖ : ℝ) : ℂ)‖ < 1 := by simpa using hz
  have hr := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hr0)
  have hre_term : ∀ n : ℕ, (((‖z‖ : ℝ) : ℂ) ^ n / (n : ℂ)).re = ‖z‖ ^ n / n := by
    intro n
    rw [show (((‖z‖ : ℝ) : ℂ) ^ n / (n : ℂ)) = (((‖z‖ ^ n / n : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hre_sum : (-Complex.log (1 - ((‖z‖ : ℝ) : ℂ))).re = -Real.log (1 - ‖z‖) := by
    rw [show (1 : ℂ) - ((‖z‖ : ℝ) : ℂ) = ((1 - ‖z‖ : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log (by linarith [norm_nonneg z])]
    simp
  simp only [hre_term, hre_sum] at hr
  refine hc.norm_le_of_bounded hr (fun n => ?_)
  rw [norm_div, norm_pow, Complex.norm_natCast]
