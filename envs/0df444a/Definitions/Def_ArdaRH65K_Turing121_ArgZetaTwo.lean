-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_ArgZetaTwo
-- name    : ArdaRH65K_Turing121_ArgZetaTwo
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:07:13.585981+00:00
-- url     : https://prove2.me/theorems/9b8ba026-1ccd-4424-9fee-3f66aac595c0
-- title:
--   ArgZetaTwo certificate definitions
-- statement:
--   This bundle defines prime-indexed logarithmic sums used at the line of real part two. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArgZetaTwo.primeLog},\;\mathtt{ArgZetaTwo.primeTerm},\;\mathtt{ArgZetaTwo.primeSum}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArgZetaTwo.lean

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

namespace ArgZetaTwo

/-! ## 1. The logarithm of the Euler product -/

/-- The prime logarithm series `L(s) = Σ_p -log(1 - p^{-s})` (principal logs). -/
noncomputable def primeLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))









/-! ## 2. The real prime sum `G = Σ_p -log(1 - p^{-2})` -/

/-- The prime term `-log(1 - p^{-2})`. -/
noncomputable def primeTerm (p : Nat.Primes) : ℝ := -Real.log (1 - (((p : ℕ) : ℝ) ^ 2)⁻¹)











/-- `G = Σ_p -log(1 - p^{-2})`. -/
noncomputable def primeSum : ℝ := ∑' p : Nat.Primes, primeTerm p















/-! ## 3. `|arg ζ(2 + i t)| ≤ G` -/















/-! ## 4. The argument change up `Re s = 2` -/









end ArgZetaTwo


def ArdaRH65K_Turing121_ArgZetaTwo : Nat := 0


