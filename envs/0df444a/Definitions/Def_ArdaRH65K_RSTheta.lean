-- Prove2me | Definitions.Def_ArdaRH65K_RSTheta
-- name    : ArdaRH65K_RSTheta
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:29:25.573284+00:00
-- url     : https://prove2.me/theorems/c4e4b629-8976-4e3d-bba7-6a13bba1ec32
-- title:
--   Auxiliary arctangent functions and theta approximation
-- statement:
--   For real $x,y,u$, this bundle defines
--
--   $$f(u)=\arctan\!\left(\frac{y}{x+u}\right),\quad
--   F(u)=(x+u)f(u)+\frac y2\log((x+u)^2+y^2),\quad
--   g(u)=-\frac{y}{(x+u)^2+y^2}.$$
--
--   It also defines the trapezoidal error from $f,F$ on each unit interval and
--   $\theta_S(t)=\frac t4\log(1/16+t^2/4)-\frac14\arctan(2t)-\frac t2-\frac t2\log\pi$.
--   Real division and logarithm use the total formal conventions. These functions
--   are used in finite bounds for the gamma phase.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RSTheta.lean

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-  RSTheta.lean -- ANDURIL Riemann-Siegel brick B0 (theta): a HEIGHT-UNIFORM kernel enclosure of
    the Riemann-Siegel phase, plus one instance at t = 280000.

    ## Provenance

    Promoted on 2026-09-23 from `Probes/RSDesign_theta.lean`, the calibration probe of the RS design
    memo (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, section 4.0 and op O-4). Every proof is
    unchanged. Two things differ from the probe:

      * The statement of the registry theorem `gaussBranch_theta_sub_thetaMain_le` now spells every
        name in full: `Filter.Tendsto`, `ThetaGap.imLnVal`, `Filter.atTop`, `nhds`. That makes it the
        verbatim text of the proposed `AND_theta_branch` statement (memo op O-4). The grant gate
        matches statement to artifact by normalized text, and the registry statement cannot rely on
        this file's `open` lines. Both spellings elaborate to the same term.
      * The trailing `#print axioms` lines moved to the guard `AxiomGuardRSTheta.lean`.

    The namespace stays `RSDesignTheta`, so names cited from the probe still resolve.

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms).

    The island's sign bridge `ZeroSignDecomp.gLine_sign_decomp_t` writes
        gLine t = M * (cos phi * Re zeta(1/2+it) - sin phi * Im zeta(1/2+it)),   M > 0,
        phi = Lam - (t/2) log pi,   Lam = lim_n imLnVal (1/4) (t/2) n,
    so every on-line sign needs a box for `phi` (= the Riemann-Siegel theta).  The existing route
    (`ForgeRate.rate_at`) bounds `|Lam - imLnVal x y n0|` by `2(|y|(x+1) + |y|^3/(3 n0))/n0`, which needs
    `n0 >> y^(3/2)` arctan terms: about 10^9 terms at t = 280000.  That is the "theta Euler route
    dies above a few hundred" wall.

    This file replaces the rate bound by a CLOSED-FORM Stirling bracket with an explicit remainder,
    valid at EVERY height, proved by an elementary convex-trapezoid argument (no Bernoulli
    functions, no polygamma, no complex Stirling, no Mathlib gap):

      * `trapezoid_convex`   : for F' = f, f' = g, g monotone on [a, a+1]:
                               0 <= (f a + f (a+1))/2 - (F (a+1) - F a) <= (g (a+1) - g a)/4.
      * `lam_bracket`        : for x > 0, y >= 0, any n0, and Lam = lim imLnVal x y:
            C - y/(4((x+n0)^2 + y^2)) <= Lam <= C,
            C = FA n0 + fA n0 / 2 - sum_{k <= n0} fA k - y,
            fA u = arctan (y/(x+u)),  FA u = (x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2).
      * `theta_bracket`      : n0 = 0, x = 1/4, y = t/2, for every t > 0:
            thetaS t - 1/(2t) <= Lam - (t/2) log pi <= thetaS t,
            thetaS t = (t/4) log (1/16 + t^2/4) - (1/4) arctan (2t) - t/2 - (t/2) log pi.
      * `theta_sub_thetaMain`, `gaussBranch_theta_sub_thetaMain_le` : against the corpus main term
            `ZeroFreeBridge.thetaMain`, |Lam - (t/2) log pi - thetaMain t| <= 1/t for every t > 0 --
            the statement DESIGN_AND_ladder_1e9 section 3.3 proposed for `AND_theta_branch` (there with
            t >= 200 and the misspelled `ZetaReflection.imLnVal`; the island name is `ThetaGap.imLnVal`).
      * `theta_280000_box`   : the numeric instance at t = 280000 (reduced mod 2 pi, K = 216236),
                               an interval of width about 2e-6 around 2.2434215934
                               (mpmath siegeltheta(280000) - 2 pi K = 2.2434215934093).

    So the theta brick of the RS era costs O(1) transcendental evaluations per point at any height
    (two logs, one arctan, log pi shared), instead of O(t^(3/2)) arctan terms.  The general
    `lam_bracket` (any x > 0) also covers the Gamma_R edge quantities Im log Gamma(x + iT/2) at
    x = 1 (sigma = 2) and, after one shift Gamma(z) = Gamma(z+1)/z, at sigma = -1.

    Calibration (the probe, 2026-09-23): 646 lines, two compile iterations. `lake env lean` took about
    20 s wall, of which kernel type checking was 0.33 s and `norm_num` elaboration 4.7 s.

    conjecture1_proved = False.  A finite enclosure of one special-function value plus a
    height-uniform inequality; nothing here bears on the Riemann Hypothesis.
-/



open Real Filter Topology Set ThetaGap

namespace RSDesignTheta

/-! ## 1.  The convex trapezoid lemma. -/





/-! ## 2.  The θ-series summand, its antiderivative and derivative. -/

/-- The summand `u ↦ arctan (y/(x+u))` of `imLnVal x y`. -/
noncomputable def fA (x y u : ℝ) : ℝ := Real.arctan (y / (x + u))

/-- Its antiderivative: `(x+u) arctan (y/(x+u)) + (y/2) log ((x+u)^2 + y^2)`. -/
noncomputable def FA (x y u : ℝ) : ℝ :=
  (x + u) * Real.arctan (y / (x + u)) + y / 2 * Real.log ((x + u) ^ 2 + y ^ 2)

/-- Its derivative: `-(y/((x+u)^2 + y^2))`. -/
noncomputable def gA (x y u : ℝ) : ℝ := -(y / ((x + u) ^ 2 + y ^ 2))









/-! ## 3.  The finite sandwich of `imLnVal`. -/

/-- The trapezoid excess on `[k, k+1]`. -/
noncomputable def eA (x y : ℝ) (k : ℕ) : ℝ :=
  (fA x y k + fA x y ((k:ℝ) + 1)) / 2 - (FA x y ((k:ℝ) + 1) - FA x y k)









/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/





/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/

/-- The closed-form Stirling value of the RS phase: `(t/4) log (1/16 + t^2/4) - (1/4) arctan (2t)
    - t/2 - (t/2) log pi`.  (Equal to `thetaMain t + 3/(16 t) + O(t^-3)`; the true phase lies in
    `[thetaS t - 1/(2t), thetaS t]`, and numerically sits at `thetaS t - 1/(6t)`.) -/
noncomputable def thetaS (t : ℝ) : ℝ :=
  t / 4 * Real.log (1 / 16 + t ^ 2 / 4) - 1 / 4 * Real.arctan (2 * t) - t / 2
    - t / 2 * Real.log Real.pi







/-! ## 6.  The numeric instance at `t = 280000` (the top of the h280000 ladder).

All constants below are short decimals chosen by an untrusted script; every inequality between
them and the exact series values is re-checked by `norm_num`/`linarith` in the kernel.  The log
brackets use Mathlib's `Real.abs_log_sub_add_sum_range_le` (Taylor series of `log (1 - x)` with the
geometric remainder `|x|^(n+1)/(1-|x|)`), the pi bracket is Mathlib's `pi_gt_d20`/`pi_lt_d20`. -/



















end RSDesignTheta


def ArdaRH65K_RSTheta : Nat := 0


