-- Prove2me | solution 1 for ArgGammaR.integral_half_re_digamma
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:07:58.892569+00:00
-- url     : https://prove2.me/submissions/109417eb-cfca-46eb-8e4d-bfaf3505c597

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
import Theorems.Thm_ArgGammaR_abs_remainder_le
import Theorems.Thm_ArgGammaR_half_re_digamma_sub_dImLn
import Theorems.Thm_DiffractionCore_digamma_continuousAt_of_re_pos
import Theorems.Thm_ThetaConverge_imLnVal_cauchy
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



theorem tendsto_gaussLam {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Tendsto (imLnVal x y) atTop (𝓝 (gaussLam x y)) :=
  (ThetaConverge.imLnVal_cauchy x y hx).tendsto_limUnder







/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/



theorem hasDerivAt_imLnVal_half {x : ℝ} (hx : 0 < x) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => imLnVal x (y / 2) n) (dImLn x n y) y := by
  unfold imLnVal dImLn
  have hlin : HasDerivAt (fun y : ℝ => y / 2 * Real.log n) (1 / 2 * Real.log n) y := by
    have := ((hasDerivAt_id y).div_const 2).mul_const (Real.log n)
    simpa using this
  have hsum : HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), Real.arctan (y / 2 / (x + k)))
      (∑ k ∈ Finset.range (n + 1), (1 / 2) * ((x + k) / ((x + k) ^ 2 + (y / 2) ^ 2))) y := by
    apply HasDerivAt.fun_sum
    intro k _
    have hxk : 0 < x + k := by positivity
    have hq : HasDerivAt (fun y : ℝ => y / 2 / (x + k)) (1 / 2 / (x + k)) y := by
      have := ((hasDerivAt_id y).div_const 2).div_const (x + k)
      simpa using this
    refine hq.arctan.congr_deriv ?_
    field_simp
  refine (hlin.sub hsum).congr_deriv ?_
  rw [mul_sub, Finset.mul_sum]

theorem continuous_dImLn {x : ℝ} (hx : 0 < x) (n : ℕ) : Continuous (dImLn x n) := by
  unfold dImLn
  refine continuous_const.mul (continuous_const.sub ?_)
  refine continuous_finsetSum _ (fun k _ => ?_)
  refine Continuous.div continuous_const (by fun_prop) (fun y => ?_)
  have : 0 < x + k := by positivity
  positivity

/-- Finite FTC: `∫_a^b dImLn = imLnVal x (b/2) n - imLnVal x (a/2) n`. -/
theorem integral_dImLn {x : ℝ} (hx : 0 < x) (n : ℕ) (a b : ℝ) :
    ∫ y in a..b, dImLn x n y = imLnVal x (b / 2) n - imLnVal x (a / 2) n :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_imLnVal_half hx n y)
    ((continuous_dImLn hx n).intervalIntegrable _ _)

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




















theorem solution {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ∫ y in a..b, (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
      = gaussLam x (b / 2) - gaussLam x (a / 2) := by
  set I0 := ∫ y in a..b, (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re
    with hI0
  set K : ℝ := (x + 2 + (|a| + |b|) / 2) / 2 * |b - a| with hK
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |(imLnVal x (b / 2) n - imLnVal x (a / 2) n) - I0| ≤ K / n := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hint1 : IntervalIntegrable
        (fun y : ℝ => (1 / 2 : ℝ) * (Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I)).re)
        MeasureTheory.volume a b := (continuous_half_re_digamma hx).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (dImLn x n) MeasureTheory.volume a b :=
      (continuous_dImLn hx n).intervalIntegrable _ _
    have hdiff : I0 - (imLnVal x (b / 2) n - imLnVal x (a / 2) n)
        = ∫ y in a..b, (1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I
            + ((n + 1 : ℕ) : ℂ))).re - Real.log n) := by
      rw [hI0, ← integral_dImLn hx n a b, ← intervalIntegral.integral_sub hint1 hint2]
      exact intervalIntegral.integral_congr (fun y _ => half_re_digamma_sub_dImLn hx n y)
    have hC : ∀ y ∈ Set.uIoc a b,
        ‖(1 / 2 : ℝ) * ((Complex.digamma ((x : ℂ) + ((y / 2 : ℝ) : ℂ) * I
            + ((n + 1 : ℕ) : ℂ))).re - Real.log n)‖ ≤ (x + 2 + (|a| + |b|) / 2) / (2 * n) := by
      intro y hy
      have hyab : |y| ≤ |a| + |b| := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hy) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b],
            by linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]⟩
      rw [Real.norm_eq_abs]
      refine le_trans (abs_remainder_le hx hn y) ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rw [← hdiff, Real.norm_eq_abs] at hnorm
    rw [abs_sub_comm]
    refine le_trans hnorm (le_of_eq ?_)
    rw [hK]
    field_simp
  have hD : Tendsto (fun n => imLnVal x (b / 2) n - imLnVal x (a / 2) n) atTop
      (𝓝 (gaussLam x (b / 2) - gaussLam x (a / 2))) :=
    (tendsto_gaussLam hx _).sub (tendsto_gaussLam hx _)
  have hD' : Tendsto (fun n => imLnVal x (b / 2) n - imLnVal x (a / 2) n) atTop (𝓝 I0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat K)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact hbound n hn
  exact tendsto_nhds_unique hD' hD
