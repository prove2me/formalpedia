-- Prove2me | solution 1 for Arb4.k6B_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:00:59.949879+00:00
-- url     : https://prove2.me/submissions/12ab4061-47ba-4a25-96b6-06e00dc60dff

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Gamma
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
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
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arb4_Q_val_div
import Theorems.Thm_Arb4_arctan_mem
import Theorems.Thm_RSDesignTheta_logpi_box
namespace Arb4.Q
end Arb4.Q
namespace RSDesignTheta
end RSDesignTheta
namespace ThetaGap
end ThetaGap
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


namespace Arb4



namespace Q





























/-! ## The value homomorphism -/

theorem den_pos (a : Q) : (0 : ℝ) < (a.dm : ℝ) + 1 := by positivity

theorem den_ne (a : Q) : (a.dm : ℝ) + 1 ≠ 0 := ne_of_gt (den_pos a)

theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]

@[simp] theorem val_ofInt (m : ℤ) : (ofInt m).val = (m : ℝ) := by
  simp [val, ofInt]

theorem cast_den_mul (a b : Q) :
    (((a.dm * b.dm + a.dm + b.dm : ℕ) : ℝ) + 1) = ((a.dm : ℝ) + 1) * ((b.dm : ℝ) + 1) := by
  push_cast; ring

theorem val_add (a b : Q) : (add a b).val = a.val + b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, add]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_sub (a b : Q) : (sub a b).val = a.val - b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, sub]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_mul (a b : Q) : (mul a b).val = a.val * b.val := by
  simp only [val, mul]
  rw [cast_den_mul]
  push_cast
  rw [mul_div_mul_comm]





theorem val_npow (a : Q) : ∀ k, (npow a k).val = a.val ^ k
  | 0 => by simp [npow, val]
  | k + 1 => by rw [npow, val_mul, val_npow a k, pow_succ]



theorem val_sumQ (f : ℕ → Q) : ∀ k, (sumQ f k).val = ∑ i ∈ Finset.range k, (f i).val
  | 0 => by simp [sumQ, val]
  | k + 1 => by rw [sumQ, val_add, val_sumQ f k, Finset.sum_range_succ]

/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr

theorem lt_sound {a b : Q} (h : lt a b = true) : a.val < b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) < b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) < (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_lt_div_iff₀ (den_pos a) (den_pos b)]
  exact hr



/-- `0 ≤ n` makes the value nonnegative. -/
theorem val_nonneg {a : Q} (hn : 0 ≤ a.n) : 0 ≤ a.val := by
  have hn' : (0 : ℝ) ≤ a.n := by exact_mod_cast hn
  exact div_nonneg hn' (den_pos a).le



/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


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















/-! ## 3.  The finite sandwich of `imLnVal`. -/











/-! ## 4.  The limit of `H n` and the Stirling bracket for `Lam`. -/





/-! ## 5.  The Riemann-Siegel phase: the `n0 = 0`, `x = 1/4`, `y = t/2` specialisation. -/









/-! ## 6.  The numeric instance at `t = 280000` (the top of the h280000 ladder).

All constants below are short decimals chosen by an untrusted script; every inequality between
them and the exact series values is re-checked by `norm_num`/`linarith` in the kernel.  The log
brackets use Mathlib's `Real.abs_log_sub_add_sum_range_le` (Taylor series of `log (1 - x)` with the
geometric remainder `|x|^(n+1)/(1-|x|)`), the pi bracket is Mathlib's `pi_gt_d20`/`pi_lt_d20`. -/

/-- `log 2` to about `7e-15` (48 terms of the `x = 1/2` series). -/
theorem log2_box :
    (3465735902799708427977/5000000000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599487910229/10000000000000000000000 := by
  have hx : |(1/2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 48
  have hl : Real.log (1 - 1/2 : ℝ) = -Real.log 2 := by
    rw [show (1:ℝ) - 1/2 = 2⁻¹ by norm_num, Real.log_inv]
  have habs : |(1/2 : ℝ)| = 1/2 := abs_of_pos (by norm_num)
  rw [hl, habs, abs_le] at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

















end RSDesignTheta


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





















/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/

















/-! ## 4. The two edge identities -/





/-! ## 5. The hypothesis-free enclosures (K6b) -/

































/-! ## 6. Rational instantiation helpers (for band emitters) -/

/-- `S2 T` from bounds on its three transcendental ingredients (`T ≥ 0`). -/
theorem S2_mem_of {T lv hv la ha lp hp : ℝ} (hT : 0 ≤ T)
    (hlog : lv ≤ Real.log (1 + T ^ 2 / 4) ∧ Real.log (1 + T ^ 2 / 4) ≤ hv)
    (hat : la ≤ Real.arctan (T / 2) ∧ Real.arctan (T / 2) ≤ ha)
    (hpi : lp ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ hp) :
    1 / 2 * la + T / 4 * lv - T / 2 - T / 2 * hp ≤ S2 T ∧
      S2 T ≤ 1 / 2 * ha + T / 4 * hv - T / 2 - T / 2 * lp := by
  unfold S2
  have h4 : 0 ≤ T / 4 := by positivity
  have h2 : 0 ≤ T / 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hlog.1 h4
  have a2 := mul_le_mul_of_nonneg_left hlog.2 h4
  have b1 := mul_le_mul_of_nonneg_left hpi.1 h2
  have b2 := mul_le_mul_of_nonneg_left hpi.2 h2
  constructor <;> linarith [hat.1, hat.2]

/-- `Sm1 T` from bounds on its three transcendental ingredients (`T ≥ 0`). -/
theorem Sm1_mem_of {T lv hv la ha lp hp : ℝ} (hT : 0 ≤ T)
    (hlog : lv ≤ Real.log (1 / 4 + T ^ 2 / 4) ∧ Real.log (1 / 4 + T ^ 2 / 4) ≤ hv)
    (hat : la ≤ Real.arctan T ∧ Real.arctan T ≤ ha)
    (hpi : lp ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ hp) :
    T / 4 * lv + la - T / 2 - T / 2 * hp ≤ Sm1 T ∧
      Sm1 T ≤ T / 4 * hv + ha - T / 2 - T / 2 * lp := by
  unfold Sm1
  have h4 : 0 ≤ T / 4 := by positivity
  have h2 : 0 ≤ T / 2 := by positivity
  have a1 := mul_le_mul_of_nonneg_left hlog.1 h4
  have a2 := mul_le_mul_of_nonneg_left hlog.2 h4
  have b1 := mul_le_mul_of_nonneg_left hpi.1 h2
  have b2 := mul_le_mul_of_nonneg_left hpi.2 h2
  constructor <;> linarith [hat.1, hat.2]



/-- The Taylor bracket of `log (1 - x)` (Mathlib's `Real.abs_log_sub_add_sum_range_le`). -/
theorem log_one_sub_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - x ^ (n + 1) / (1 - x) ≤ Real.log (1 - x) ∧
      Real.log (1 - x) ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + x ^ (n + 1) / (1 - x) := by
  have hx : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_of_nonneg hx0, abs_le] at h
  constructor <;> linarith [h.1, h.2]

end ArgGammaR


/-  Arb4_Gamma.lean -- lane Arb4 (h1000 compaction): the Γℝ argument-change side conditions of a
    Turing band (brick K6b, `ArgGammaR`) as ONE Boolean kernel check.

    `ArgChangeGlue.K6Side` compares the band's enclosures `[L4, H4]`, `[L5, H5]` with the closed-form
    brackets `Sm1`, `S2` of `ArgGammaR` at the two edge heights.  The generated module
    `ArgChangeH1000` proves one `log` box, one `arctan` box and one `S2`/`Sm1` box per height by
    `norm_num` over truncated series (about 1 MB of olean per height).  Here:

      * `logOK logLo logHi`, `log_mem`  -- `log v = k log 2 + log (1 - x)`, `v = 2^k (1 - x)`,
                             `0 ≤ x < 1`, with `RSDesignTheta.log2_box` and the Taylor bracket
                             `ArgGammaR.log_one_sub_mem` (n terms);
      * `atanOK arctanLo arctanHi`, `arctan_mem` -- `arctan y` by the Taylor bracket
                             `ArctanTaylor.arctan_bracket` (mode 0, `0 ≤ y ≤ 1`), by
                             `arctan y = π/2 - arctan (1/y)` (mode 1, `y > 0`), or `π/4` (`y = 1`);
      * `GamD`, `gamOK`, `S2_mem`, `Sm1_mem` -- the brackets at one height (`ArgGammaR.S2_mem_of`,
                             `Sm1_mem_of`, `RSDesignTheta.logpi_box`, `π` to 20 digits);
      * `k6B`, `k6B_sound` -- the four K6b comparisons of a band from two heights.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/



open scoped Real

namespace Arb4

open Q

/-! ## A. Constants -/










theorem log2_mem : l2lo.val ≤ Real.log 2 ∧ Real.log 2 ≤ l2hi.val := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.log2_box
  rw [l2lo, l2hi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  exact ⟨h1, h2⟩

theorem logpi_mem : lplo.val ≤ Real.log π ∧ Real.log π ≤ lphi.val := by
  obtain ⟨h1, h2⟩ := RSDesignTheta.logpi_box
  rw [lplo, lphi, val_frac _ (by norm_num), val_frac _ (by norm_num)]
  push_cast
  exact ⟨h1, h2⟩



/-! ## B. Logarithms -/



theorem val_pow2Q (k : ℤ) : (pow2Q k).val = (2 : ℝ) ^ k := by
  unfold pow2Q
  by_cases h : 0 ≤ k
  · rw [if_pos h, val_ofNat]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    push_cast
    simp
  · rw [if_neg h, val_frac _ Nat.one_le_two_pow]
    push Not at h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = m := ⟨(-k).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hk : k = -(m : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast]
    simp

theorem pow2Q_n_pos (k : ℤ) : 0 < (pow2Q k).n := by
  unfold pow2Q
  by_cases h : 0 ≤ k
  · rw [if_pos h]; show (0 : ℤ) < ((2 ^ k.toNat : ℕ) : ℤ); exact_mod_cast Nat.two_pow_pos _
  · rw [if_neg h]; show (0 : ℤ) < 1; norm_num



theorem val_lserQ (x : Q) (n : ℕ) :
    (lserQ x n).val = ∑ i ∈ Finset.range n, x.val ^ (i + 1) / (i + 1) := by
  rw [lserQ, val_sumQ]
  apply Finset.sum_congr rfl
  intro i _
  rw [val_div _ (by show (0 : ℤ) < ((i + 1 : ℕ) : ℤ); exact_mod_cast Nat.succ_pos i), val_npow,
    val_ofNat]
  push_cast; ring








theorem kl2_mem (k : ℤ) : (kl2lo k).val ≤ k * Real.log 2 ∧ k * Real.log 2 ≤ (kl2hi k).val := by
  obtain ⟨h1, h2⟩ := log2_mem
  unfold kl2lo kl2hi
  by_cases h : 0 ≤ k
  · rw [if_pos h, if_pos h, val_mul, val_mul, val_ofInt]
    have hk : (0 : ℝ) ≤ k := by exact_mod_cast h
    exact ⟨mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hk⟩
  · rw [if_neg h, if_neg h, val_mul, val_mul, val_ofInt]
    have hk : (k : ℝ) ≤ 0 := by push Not at h; exact_mod_cast h.le
    exact ⟨mul_le_mul_of_nonpos_left h2 hk, mul_le_mul_of_nonpos_left h1 hk⟩



theorem omx_n_pos {x : Q} (h : lt x (ofNat 1) = true) : 0 < (omx x).n := by
  have h' : x.n * ((0 : ℕ) + 1 : ℤ) < ((1 : ℕ) : ℤ) * ((x.dm : ℤ) + 1) := of_decide_eq_true h
  show 0 < ((1 : ℕ) : ℤ) * ((x.dm : ℤ) + 1) - x.n * ((0 : ℕ) + 1 : ℤ)
  linarith





theorem log_mem (v : Q) (k : ℤ) (n : ℕ) (h : logOK v k = true) :
    (logLo v k n).val ≤ Real.log v.val ∧ Real.log v.val ≤ (logHi v k n).val := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hx0⟩, hx1⟩ := h
  set x := lx v k with hx
  have hv' := lt_sound hv
  rw [val_ofNat, Nat.cast_zero] at hv'
  have hx0' : 0 ≤ x.val := val_nonneg hx0
  have hx1' := lt_sound hx1
  rw [val_ofNat, Nat.cast_one] at hx1'
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hxv : x.val = 1 - v.val / (2 : ℝ) ^ k := by
    rw [hx, lx, val_sub, val_ofNat, val_div _ (pow2Q_n_pos k), val_pow2Q, Nat.cast_one]
  have hveq : v.val = (2 : ℝ) ^ k * (1 - x.val) := by
    rw [hxv]; field_simp; ring
  have hpos1 : (0 : ℝ) < 1 - x.val := by linarith
  have hlog : Real.log v.val = k * Real.log 2 + Real.log (1 - x.val) := by
    rw [hveq, Real.log_mul (ne_of_gt h2k) (ne_of_gt hpos1), Real.log_zpow]
  have hser := ArgGammaR.log_one_sub_mem hx0' hx1' n
  have hk := kl2_mem k
  have homx : (omx x).val = 1 - x.val := by rw [omx, val_sub, val_ofNat, Nat.cast_one]
  have hdiv : (div (npow x (n + 1)) (omx x)).val = x.val ^ (n + 1) / (1 - x.val) := by
    rw [val_div _ (omx_n_pos hx1), val_npow, homx]
  unfold logLo logHi
  rw [← hx, val_sub, val_sub, val_add, val_sub, val_lserQ, hdiv, hlog]
  constructor <;> linarith [hser.1, hser.2, hk.1, hk.2]

/-! ## C. Arctangents -/



















theorem two_n_pos : 0 < (ofNat 2).n := by show (0 : ℤ) < ((2 : ℕ) : ℤ); norm_num
theorem four_n_pos : 0 < (ofNat 4).n := by show (0 : ℤ) < ((4 : ℕ) : ℤ); norm_num



/-! ## D. The closed-form Γℝ brackets at one height -/



namespace GamD







theorem val_v2 (G : GamD) : G.v2.val = 1 + G.T.val ^ 2 / 4 := by
  rw [v2, val_add, val_ofNat, val_div _ four_n_pos, val_npow, val_ofNat]; push_cast; ring

theorem val_vm (G : GamD) : G.vm.val = 1 / 4 + G.T.val ^ 2 / 4 := by
  rw [vm, val_add, val_frac _ (by norm_num), val_div _ four_n_pos, val_npow, val_ofNat]
  push_cast; ring

theorem val_half (G : GamD) : G.half.val = G.T.val / 2 := by
  rw [half, val_div _ two_n_pos, val_ofNat]; push_cast; ring

end GamD











theorem S2_mem (G : GamD) (h : gamOK G = true) :
    (S2lo G).val ≤ ArgGammaR.S2 G.T.val ∧ ArgGammaR.S2 G.T.val ≤ (S2hi G).val := by
  simp only [gamOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hT, hl2⟩, _⟩, ha2⟩, _⟩ := h
  have hT' := le_sound hT
  rw [val_ofNat, Nat.cast_zero] at hT'
  have hl := log_mem G.v2 G.k2 G.n2 hl2
  rw [G.val_v2] at hl
  have ha := arctan_mem G.half G.N2 G.md2 ha2
  rw [G.val_half] at ha
  have hm := ArgGammaR.S2_mem_of hT' hl ha logpi_mem
  unfold S2lo S2hi
  simp only [val_sub, val_add, val_mul, val_div _ four_n_pos, val_div _ two_n_pos,
    val_frac 1 (by norm_num : 1 ≤ 2), val_ofNat]
  push_cast
  constructor <;> linarith [hm.1, hm.2]

theorem Sm1_mem (G : GamD) (h : gamOK G = true) :
    (Sm1lo G).val ≤ ArgGammaR.Sm1 G.T.val ∧ ArgGammaR.Sm1 G.T.val ≤ (Sm1hi G).val := by
  simp only [gamOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hT, _⟩, hlm⟩, _⟩, ham⟩ := h
  have hT' := le_sound hT
  rw [val_ofNat, Nat.cast_zero] at hT'
  have hl := log_mem G.vm G.km G.nm hlm
  rw [G.val_vm] at hl
  have ha := arctan_mem G.T G.Nm G.mdm ham
  have hm := ArgGammaR.Sm1_mem_of hT' hl ha logpi_mem
  unfold Sm1lo Sm1hi
  simp only [val_sub, val_add, val_mul, val_div _ four_n_pos, val_div _ two_n_pos, val_ofNat]
  push_cast
  constructor <;> linarith [hm.1, hm.2]

/-! ## E. The K6b comparisons of a band -/





theorem npow_two_nonneg_n (T : Q) : 0 ≤ (npow T 2).n := by
  show 0 ≤ 1 * T.n * T.n
  rw [one_mul]; exact mul_self_nonneg _

theorem val_em1Q (T : Q) : (em1Q T).val = ArgGammaR.em1 T.val := by
  have hpos : 0 < (mul (ofNat 2) (add (ofNat 1) (npow T 2))).n := by
    show 0 < ((2 : ℕ) : ℤ) * (((1 : ℕ) : ℤ) * ((npow T 2).dm + 1 : ℤ) + (npow T 2).n * ((0 : ℕ) + 1 : ℤ))
    have := npow_two_nonneg_n T
    positivity
  rw [em1Q, val_div _ hpos, val_mul, val_add, val_npow, val_ofNat, val_ofNat, ArgGammaR.em1]
  push_cast; ring

theorem val_e2Q (T : Q) : (e2Q T).val = ArgGammaR.e2 T.val := by
  have hpos : 0 < (mul (ofNat 2) (add (ofNat 4) (npow T 2))).n := by
    show 0 < ((2 : ℕ) : ℤ) * (((4 : ℕ) : ℤ) * ((npow T 2).dm + 1 : ℤ) + (npow T 2).n * ((0 : ℕ) + 1 : ℤ))
    have := npow_two_nonneg_n T
    positivity
  rw [e2Q, val_div _ hpos, val_mul, val_add, val_npow, val_ofNat, val_ofNat, ArgGammaR.e2]
  push_cast; ring





end Arb4


/-  Arb4_Gamma.lean -- lane Arb4 (h1000 compaction): the Γℝ argument-change side conditions of a
    Turing band (brick K6b, `ArgGammaR`) as ONE Boolean kernel check.

    `ArgChangeGlue.K6Side` compares the band's enclosures `[L4, H4]`, `[L5, H5]` with the closed-form
    brackets `Sm1`, `S2` of `ArgGammaR` at the two edge heights.  The generated module
    `ArgChangeH1000` proves one `log` box, one `arctan` box and one `S2`/`Sm1` box per height by
    `norm_num` over truncated series (about 1 MB of olean per height).  Here:

      * `logOK logLo logHi`, `log_mem`  -- `log v = k log 2 + log (1 - x)`, `v = 2^k (1 - x)`,
                             `0 ≤ x < 1`, with `RSDesignTheta.log2_box` and the Taylor bracket
                             `ArgGammaR.log_one_sub_mem` (n terms);
      * `atanOK arctanLo arctanHi`, `arctan_mem` -- `arctan y` by the Taylor bracket
                             `ArctanTaylor.arctan_bracket` (mode 0, `0 ≤ y ≤ 1`), by
                             `arctan y = π/2 - arctan (1/y)` (mode 1, `y > 0`), or `π/4` (`y = 1`);
      * `GamD`, `gamOK`, `S2_mem`, `Sm1_mem` -- the brackets at one height (`ArgGammaR.S2_mem_of`,
                             `Sm1_mem_of`, `RSDesignTheta.logpi_box`, `π` to 20 digits);
      * `k6B`, `k6B_sound` -- the four K6b comparisons of a band from two heights.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/



open scoped Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. Constants -/
















/-! ## B. Logarithms -/






























/-! ## C. Arctangents -/
























/-! ## D. The closed-form Γℝ brackets at one height -/



section
namespace Arb4.GamD
end Arb4.GamD
open Arb4.GamD













end















/-! ## E. The K6b comparisons of a band -/













theorem solution (G0 G1 : GamD) (L4 H4 L5 H5 : Q) (h : k6B G0 G1 L4 H4 L5 H5 = true) :
    0 ≤ G0.T.val ∧ 0 ≤ G1.T.val ∧
      L4.val ≤ ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val - ArgGammaR.em1 G1.T.val ∧
      ArgGammaR.Sm1 G1.T.val - ArgGammaR.Sm1 G0.T.val + ArgGammaR.em1 G0.T.val ≤ H4.val ∧
      L5.val ≤ ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val - ArgGammaR.e2 G1.T.val ∧
      ArgGammaR.S2 G1.T.val - ArgGammaR.S2 G0.T.val + ArgGammaR.e2 G0.T.val ≤ H5.val := by
  simp only [k6B, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, hL4⟩, hH4⟩, hL5⟩, hH5⟩ := h
  have a0 := Sm1_mem G0 h0
  have a1 := Sm1_mem G1 h1
  have b0 := S2_mem G0 h0
  have b1 := S2_mem G1 h1
  have hT0 : 0 ≤ G0.T.val := by
    have := h0
    simp only [gamOK, Bool.and_eq_true] at this
    have h' := le_sound this.1.1.1.1
    rw [val_ofNat, Nat.cast_zero] at h'
    exact h'
  have hT1 : 0 ≤ G1.T.val := by
    have := h1
    simp only [gamOK, Bool.and_eq_true] at this
    have h' := le_sound this.1.1.1.1
    rw [val_ofNat, Nat.cast_zero] at h'
    exact h'
  have l4 := le_sound hL4
  have h4 := le_sound hH4
  have l5 := le_sound hL5
  have h5 := le_sound hH5
  rw [val_sub, val_sub, val_em1Q] at l4
  rw [val_add, val_sub, val_em1Q] at h4
  rw [val_sub, val_sub, val_e2Q] at l5
  rw [val_add, val_sub, val_e2Q] at h5
  refine ⟨hT0, hT1, ?_, ?_, ?_, ?_⟩ <;> linarith [a0.1, a0.2, a1.1, a1.2, b0.1, b0.2, b1.1, b1.2]
