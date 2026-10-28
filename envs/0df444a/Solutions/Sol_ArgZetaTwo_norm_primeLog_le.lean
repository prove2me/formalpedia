-- Prove2me | solution 1 for ArgZetaTwo.norm_primeLog_le
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:47:07.921141+00:00
-- url     : https://prove2.me/submissions/048620a2-2005-445c-b53e-bc13b678f886

import Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib
import Theorems.Thm_ArgZetaTwo_norm_neg_log_one_sub_le
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







/-- `-log(1 - x) ≤ 2 x` for `0 ≤ x ≤ 1/2`. -/
theorem neg_log_one_sub_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have h1 : -Real.log (1 - x) = Real.log (1 - x)⁻¹ := by rw [Real.log_inv]
  have h2 : Real.log (1 - x)⁻¹ ≤ (1 - x)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith
  linarith

/-- `0 ≤ -log(1 - x)` for `0 ≤ x < 1`. -/
theorem neg_log_one_sub_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) : 0 ≤ -Real.log (1 - x) := by
  have : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/



theorem prime_inv_sq_le (p : Nat.Primes) : (((p : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
  have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have h4 : (4 : ℝ) ≤ ((p : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4

theorem prime_inv_sq_nonneg (p : Nat.Primes) : 0 ≤ (((p : ℕ) : ℝ) ^ 2)⁻¹ := by positivity

theorem primeTerm_nonneg (p : Nat.Primes) : 0 ≤ primeTerm p :=
  neg_log_one_sub_nonneg (prime_inv_sq_nonneg p) (by linarith [prime_inv_sq_le p])

theorem summable_prime_inv_sq : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
  have h := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
  refine h.congr (fun p => ?_)
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Real.rpow_neg hp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem summable_primeTerm : Summable primeTerm := by
  refine Summable.of_nonneg_of_le primeTerm_nonneg (fun p => ?_) (summable_prime_inv_sq.mul_left 2)
  exact neg_log_one_sub_le_two_mul (prime_inv_sq_nonneg p) (by linarith [prime_inv_sq_le p])



theorem hasSum_primeTerm : HasSum primeTerm primeSum := summable_primeTerm.hasSum













/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/















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




theorem solution (t : ℝ) : ‖primeLog ((2 : ℂ) + (t : ℂ) * I)‖ ≤ primeSum := by
  unfold primeLog
  refine tsum_of_norm_bounded hasSum_primeTerm (fun p => ?_)
  have hnorm : ‖((p : ℕ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ = (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
    have hre : (-((2 : ℂ) + (t : ℂ) * I)).re = -2 := by simp
    rw [hre, Real.rpow_neg (Nat.cast_nonneg _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have hlt : ‖((p : ℕ) : ℂ) ^ (-((2 : ℂ) + (t : ℂ) * I))‖ < 1 := by
    rw [hnorm]; linarith [prime_inv_sq_le p]
  have h := norm_neg_log_one_sub_le hlt
  rw [hnorm] at h
  exact h
