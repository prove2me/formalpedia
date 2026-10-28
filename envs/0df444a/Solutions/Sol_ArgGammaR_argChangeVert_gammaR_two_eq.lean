-- Prove2me | solution 1 for ArgGammaR.argChangeVert_gammaR_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:10:38.155563+00:00
-- url     : https://prove2.me/submissions/596beaa8-15d0-4426-8f9f-6520d018089f

import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
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
import Theorems.Thm_ArgGammaR_integral_half_re_digamma
import Theorems.Thm_DiffractionCore_continuous_logDeriv_gammaR_vLine
import Theorems.Thm_DiffractionCore_digamma_continuousAt_of_re_pos
import Theorems.Thm_ZeroFreeBridge_logDeriv_gammaR
namespace RSDesignTheta
end RSDesignTheta
namespace ThetaGap
end ThetaGap
/-  ArgGammaR.lean -- brick K6b of the ANDURIL Arb discharge (with the T6 bridge it needs)
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2f, bricks K6b and T6).

    THE BINDERS IT DISCHARGES.  Conjuncts 8 and 9 of the `hArbT` binder of every emitted Turing
    band (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4,
        hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5,

    the argument changes of the archimedean factor `Γℝ(s) = π^{-s/2} Γ(s/2)` up the two vertical
    edges of the RvM rectangle.  The emitted bands feed them 1e-12-wide Arb enclosures.  This file
    proves them HYPOTHESIS-FREE for every `0 ≤ T0`, `0 ≤ T1`, with explicit elementary endpoints
    (logs and arctans), in the exact binder form:

        argChangeVert Γℝ 2 T0 T1    ∈ [S2 T1 - S2 T0 - e2 T1,  S2 T1 - S2 T0 + e2 T0]    (`hAG2_closed`)
        argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0] (`hAG1_closed`)

        S2 T  = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π,   e2 T  = T/(2(4 + T²)),
        Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π,          em1 T = T/(2(1 + T²)),

    plus the sharper `hAG2_mem` / `hAG1_mem` at any Stirling base index `n0` (error
    `y/(4((x+n0)² + y²))` at each edge, `y = T/2`), for the lowest bands.

    THE T6 BRIDGE (`integral_half_re_digamma`).  `RSTheta.lam_bracket` brackets the GAUSS BRANCH
    `Λ(x, y) = lim_n imLnVal x y n` (`gaussLam`), a limit of arctan sums.  The binders are integrals
    of `logDeriv Γℝ`.  The bridge identifies them: for `x > 0` and all `a`, `b`,

        ∫_a^b (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2),

    proved WITHOUT any locally-uniform-convergence machinery:
      * finite FTC: `d/dy imLnVal x (y/2) n = (1/2)(log n - Σ_{k≤n} (x+k)/((x+k)² + (y/2)²))`;
      * `ZeroFreeBridge.digamma_shift`: Re ψ(z) = [that sum] + Re(ψ(z + n + 1) - log n);
      * the remainder is at most `(x + 2 + |y|/2)/(2n)` (Binet bound
        `ZeroFreeBridge.norm_digamma_sub_log_le` at `Re ≥ 2` plus `log u ≤ u - 1`), so its
        integral is `O(1/n)`, and uniqueness of limits closes the identity.
    Then `logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` gives the σ = 2 edge at `x = 1`, and at σ = -1
    the shift `ψ(z) = ψ(z+1) - 1/z` (`z = -1/2 + i y/2`) gives `x = 1/2` plus the elementary
    `∫ 1/(1 + y²) = arctan T1 - arctan T0`.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Elementary enclosures of the Γ-factor edges of a finite zero
    count; nothing here bears on the Riemann Hypothesis. -/




open Complex Filter Topology
open ThetaGap RSDesignTheta

namespace ArgGammaR

/-! ## 1. The Gauss-branch limit `Λ(x, y)` -/











/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/









/-- The digamma ray point `x + i y/2`. -/
theorem ray_re (x y : ℝ) : ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I).re = x := by simp

theorem continuous_half_re_digamma {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re) := by
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hpath : Continuous (fun y : ℝ => (x : ℂ) + ((y / 2 : ℝ) : ℂ) * I) := by fun_prop
  exact ContinuousAt.comp (g := Complex.digamma)
    (DiffractionCore.digamma_continuousAt_of_re_pos (by rw [ray_re]; exact hx))
    hpath.continuousAt









/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/



/-- `σ = 2`: `Re logDeriv Γℝ(2 + i y) = -(log π)/2 + (1/2) Re ψ(1 + i y/2)`. -/
theorem re_logDeriv_gammaR_two (y : ℝ) :
    (logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = -(Real.log Real.pi) / 2
        + (1 / 2 : ℝ) * (Complex.digamma (((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re := by
  have hhalf : (((2 : ℝ) : ℂ) + (y : ℂ) * I) / 2 = ((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hs : 0 < ((((2 : ℝ) : ℂ) + (y : ℂ) * I) / 2).re := by rw [hhalf]; simp
  rw [ZeroFreeBridge.logDeriv_gammaR _ hs, hhalf]
  have h1 : (-(Real.log Real.pi : ℂ) / 2) = ((-(Real.log Real.pi) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]













/-! ## 4. The two edge identities -/





/-! ## 5. The hypothesis-free enclosures (K6b) -/

































/-! ## 6. Rational instantiation helpers (for band emitters) -/









end ArgGammaR


/-  ArgGammaR.lean -- brick K6b of the ANDURIL Arb discharge (with the T6 bridge it needs)
    (telperion/docs/ANDURIL_ARB_DISCHARGE_2026-09-23.md, inventory row H2f, bricks K6b and T6).

    THE BINDERS IT DISCHARGES.  Conjuncts 8 and 9 of the `hArbT` binder of every emitted Turing
    band (`TuringBand.BandStatement`, `BandGlue.BandData.EnclHyp`) are

        hAG1 : DiffractionCore.argChangeVert Gammaℝ (-1) T0 T1 ∈ Set.Icc L4 H4,
        hAG2 : DiffractionCore.argChangeVert Gammaℝ 2 T0 T1 ∈ Set.Icc L5 H5,

    the argument changes of the archimedean factor `Γℝ(s) = π^{-s/2} Γ(s/2)` up the two vertical
    edges of the RvM rectangle.  The emitted bands feed them 1e-12-wide Arb enclosures.  This file
    proves them HYPOTHESIS-FREE for every `0 ≤ T0`, `0 ≤ T1`, with explicit elementary endpoints
    (logs and arctans), in the exact binder form:

        argChangeVert Γℝ 2 T0 T1    ∈ [S2 T1 - S2 T0 - e2 T1,  S2 T1 - S2 T0 + e2 T0]    (`hAG2_closed`)
        argChangeVert Γℝ (-1) T0 T1 ∈ [Sm1 T1 - Sm1 T0 - em1 T1, Sm1 T1 - Sm1 T0 + em1 T0] (`hAG1_closed`)

        S2 T  = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π,   e2 T  = T/(2(4 + T²)),
        Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π,          em1 T = T/(2(1 + T²)),

    plus the sharper `hAG2_mem` / `hAG1_mem` at any Stirling base index `n0` (error
    `y/(4((x+n0)² + y²))` at each edge, `y = T/2`), for the lowest bands.

    THE T6 BRIDGE (`integral_half_re_digamma`).  `RSTheta.lam_bracket` brackets the GAUSS BRANCH
    `Λ(x, y) = lim_n imLnVal x y n` (`gaussLam`), a limit of arctan sums.  The binders are integrals
    of `logDeriv Γℝ`.  The bridge identifies them: for `x > 0` and all `a`, `b`,

        ∫_a^b (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2),

    proved WITHOUT any locally-uniform-convergence machinery:
      * finite FTC: `d/dy imLnVal x (y/2) n = (1/2)(log n - Σ_{k≤n} (x+k)/((x+k)² + (y/2)²))`;
      * `ZeroFreeBridge.digamma_shift`: Re ψ(z) = [that sum] + Re(ψ(z + n + 1) - log n);
      * the remainder is at most `(x + 2 + |y|/2)/(2n)` (Binet bound
        `ZeroFreeBridge.norm_digamma_sub_log_le` at `Re ≥ 2` plus `log u ≤ u - 1`), so its
        integral is `O(1/n)`, and uniqueness of limits closes the identity.
    Then `logDeriv Γℝ s = -(log π)/2 + (1/2) ψ(s/2)` gives the σ = 2 edge at `x = 1`, and at σ = -1
    the shift `ψ(z) = ψ(z+1) - 1/z` (`z = -1/2 + i y/2`) gives `x = 1/2` plus the elementary
    `∫ 1/(1 + y²) = arctan T1 - arctan T0`.

    Trust: no hypotheses beyond those stated; axioms [propext, Classical.choice, Quot.sound]
    (see AxiomGuardArgChange.lean).  No `sorry`.

    conjecture1_proved = False.  Elementary enclosures of the Γ-factor edges of a finite zero
    count; nothing here bears on the Riemann Hypothesis. -/




open Complex Filter Topology
open ThetaGap RSDesignTheta

section
namespace ArgGammaR
end ArgGammaR
open ArgGammaR

/-! ## 1. The Gauss-branch limit `Λ(x, y)` -/











/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/





















/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/

















/-! ## 4. The two edge identities -/


theorem solution (T0 T1 : ℝ) :
    DiffractionCore.argChangeVert Gammaℝ 2 T0 T1
      = (gaussLam 1 (T1 / 2) - T1 / 2 * Real.log Real.pi)
        - (gaussLam 1 (T0 / 2) - T0 / 2 * Real.log Real.pi) := by
  have hcont := DiffractionCore.continuous_logDeriv_gammaR_vLine (σ := 2) (by norm_num)
  have hInt : IntervalIntegrable (fun y : ℝ => logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume T0 T1 := hcont.intervalIntegrable _ _
  have hre := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hInt
  simp only [RCLike.re_to_complex] at hre
  unfold DiffractionCore.argChangeVert
  rw [← hre]
  have hcongr : ∫ y in T0..T1, (logDeriv Gammaℝ (((2 : ℝ) : ℂ) + (y : ℂ) * I)).re
      = ∫ y in T0..T1, (-(Real.log Real.pi) / 2
          + (1 / 2 : ℝ) * (Complex.digamma (((1 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re) :=
    intervalIntegral.integral_congr (fun y _ => re_logDeriv_gammaR_two y)
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_half_re_digamma (x := 1) (by norm_num)).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_half_re_digamma (x := 1) (by norm_num), smul_eq_mul]
  ring
