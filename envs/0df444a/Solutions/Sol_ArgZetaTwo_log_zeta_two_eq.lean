-- Prove2me | solution 1 for ArgZetaTwo.log_zeta_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:53.188988+00:00
-- url     : https://prove2.me/submissions/0a0e193c-b54f-4528-8b67-6fad67c07aaf

import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ArgZetaTwo_log_pi_sq_div_six_lt
import Theorems.Thm_ArgZetaTwo_norm_primeLog_le
import Theorems.Thm_ArgZetaTwo_primeLog_two
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



/-- The Euler product in exponential form (Mathlib). -/
theorem exp_primeLog {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeLog s) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs







/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/



















/-- `exp G = π²/6`: the Euler product at the real point `2`. -/
theorem exp_primeSum : Real.exp primeSum = Real.pi ^ 2 / 6 := by
  have h := exp_primeLog (s := 2) (by norm_num)
  rw [primeLog_two, riemannZeta_two, ← Complex.ofReal_exp] at h
  exact_mod_cast h

/-- `G = log (π²/6) = log ζ(2)`. -/
theorem primeSum_eq : primeSum = Real.log (Real.pi ^ 2 / 6) := by
  rw [← exp_primeSum, Real.log_exp]



theorem primeSum_lt : primeSum < 249 / 500 := by
  rw [primeSum_eq]; exact log_pi_sq_div_six_lt



/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/

/-- The point `2 + i t`. -/
theorem re_two_add (t : ℝ) : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp













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






theorem solution (t : ℝ) :
    Complex.log (riemannZeta ((2 : ℂ) + (t : ℂ) * I)) = primeLog ((2 : ℂ) + (t : ℂ) * I) := by
  set L := primeLog ((2 : ℂ) + (t : ℂ) * I) with hL
  have hexp : Complex.exp L = riemannZeta ((2 : ℂ) + (t : ℂ) * I) :=
    exp_primeLog (by rw [re_two_add]; norm_num)
  have hn := norm_primeLog_le t
  rw [← hL] at hn
  have him : |L.im| ≤ primeSum := le_trans (Complex.abs_im_le_norm L) hn
  have hG := primeSum_lt
  have hpi : (249 / 500 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  rw [← hexp]
  apply Complex.log_exp
  · linarith [(abs_le.mp him).1]
  · linarith [(abs_le.mp him).2]
