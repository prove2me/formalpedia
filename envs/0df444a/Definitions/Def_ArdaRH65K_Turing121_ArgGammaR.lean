-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_ArgGammaR
-- name    : ArdaRH65K_Turing121_ArgGammaR
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:06:57.43582+00:00
-- url     : https://prove2.me/theorems/348b9702-e8be-4df3-ac92-ee2e2a90b35e
-- title:
--   ArgGammaR certificate definitions
-- statement:
--   This bundle defines the gamma-factor phase and real auxiliary expressions for argument changes. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ArgGammaR.gaussLam},\;\mathtt{ArgGammaR.lamC},\;\mathtt{ArgGammaR.lamE},\;\mathtt{ArgGammaR.dImLn}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ArgGammaR.lean

import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
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

/-- The Gauss-branch value `Λ(x, y) = lim_n imLnVal x y n` (informally Im log Γ(x + i y) on the
    branch continuous from the real axis; `ThetaConverge.imLnVal_cauchy` gives the limit for
    `x > 0`, and `ThetaConverge.convergence_obligation` shows it is an argument of Γ(x + i y)). -/
noncomputable def gaussLam (x y : ℝ) : ℝ := limUnder atTop (imLnVal x y)



/-- The Stirling bracket centre of `RSTheta.lam_bracket` at base index `n0`. -/
noncomputable def lamC (x y : ℝ) (n0 : ℕ) : ℝ :=
  FA x y n0 + fA x y n0 / 2 - ∑ k ∈ Finset.range (n0 + 1), fA x y k - y

/-- The Stirling bracket width of `RSTheta.lam_bracket` at base index `n0`. -/
noncomputable def lamE (x y : ℝ) (n0 : ℕ) : ℝ := y / (4 * ((x + n0) ^ 2 + y ^ 2))



/-! ## 2. The T6 bridge: `∫ (1/2) Re ψ(x + i y/2) dy = Λ(x, b/2) - Λ(x, a/2)` -/

/-- The derivative in `y` of `imLnVal x (y/2) n`. -/
noncomputable def dImLn (x : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  (1 / 2) * (Real.log n - ∑ k ∈ Finset.range (n + 1), (x + k) / ((x + k) ^ 2 + (y / 2) ^ 2))



















/-! ## 3. `logDeriv Γℝ` on the two vertical edges -/

















/-! ## 4. The two edge identities -/





/-! ## 5. The hypothesis-free enclosures (K6b) -/

/-- The σ = 2 Γℝ phase main term at base index `n0`: `lamC 1 (T/2) n0 - (T/2) log π`. -/
noncomputable def phase2 (n0 : ℕ) (T : ℝ) : ℝ := lamC 1 (T / 2) n0 - T / 2 * Real.log Real.pi

/-- The σ = -1 Γℝ phase main term at base index `n0`:
    `lamC (1/2) (T/2) n0 + arctan T - (T/2) log π`. -/
noncomputable def phaseM1 (n0 : ℕ) (T : ℝ) : ℝ :=
  lamC (1 / 2) (T / 2) n0 + Real.arctan T - T / 2 * Real.log Real.pi





/-- The closed-form σ = 2 phase (`n0 = 0`):
    `S2 T = (1/2) arctan (T/2) + (T/4) log (1 + T²/4) - T/2 - (T/2) log π`. -/
noncomputable def S2 (T : ℝ) : ℝ :=
  1 / 2 * Real.arctan (T / 2) + T / 4 * Real.log (1 + T ^ 2 / 4) - T / 2
    - T / 2 * Real.log Real.pi

/-- The closed-form σ = -1 phase (`n0 = 0`):
    `Sm1 T = (T/4) log (1/4 + T²/4) + arctan T - T/2 - (T/2) log π`. -/
noncomputable def Sm1 (T : ℝ) : ℝ :=
  T / 4 * Real.log (1 / 4 + T ^ 2 / 4) + Real.arctan T - T / 2 - T / 2 * Real.log Real.pi

/-- The σ = 2 edge error (`n0 = 0`): `e2 T = T/(2(4 + T²))`. -/
noncomputable def e2 (T : ℝ) : ℝ := T / (2 * (4 + T ^ 2))

/-- The σ = -1 edge error (`n0 = 0`): `em1 T = T/(2(1 + T²))`. -/
noncomputable def em1 (T : ℝ) : ℝ := T / (2 * (1 + T ^ 2))

















/-! ## 6. Rational instantiation helpers (for band emitters) -/









end ArgGammaR


def ArdaRH65K_Turing121_ArgGammaR : Nat := 0


