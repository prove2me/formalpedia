-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
-- name    : ArdaRH65K_Turing121_EMZetaOfflineCore
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:05:57.397262+00:00
-- url     : https://prove2.me/theorems/4841f9e3-811e-4a37-bbc3-5cabe4589d8b
-- title:
--   EMZetaOfflineCore certificate definitions
-- statement:
--   This bundle defines the truncated sawtooth function used by the offline Euler–Maclaurin argument. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ZetaReflection.EMOff.sawCut}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineCore.lean

import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
/-  EMZetaOfflineCore.lean -- lane offline (ANDURIL Arb discharge, memo ANDURIL_ARB_DISCHARGE_2026-09-23
    brick B6 / K2): the general-order Euler-Maclaurin representation of ζ OFF the critical line.

    `EMZetaHigh.em_zeta_order` proves the order-`m` identity
        ζ(s) = emFiniteM m s N + (-1)^(m-1) · emTail s N m / m!
    on `Re s > 0` only (it is transported from the K = 1 continuation `em_zeta_strip`).  The tail
    integral converges on the larger half-plane `Re s > 1 - m`, so the identity extends there by the
    identity theorem.  This file proves that extension and the resulting remainder bounds for
    every real part `σ > 1 - 2K` (even saw) and `σ > -2K` (odd saw):

      O1.  `emTail_eq_mellin`        -- the tail is `emC s m · mellin (sawCut m N) (1 - s - m)`;
      O2.  `emTail_differentiableAt` -- hence complex-differentiable on `Re s > 1 - m`
                                        (`mellin_differentiableAt_of_isBigO_rpow`);
      O3.  `emFiniteM_differentiableAt` -- the finite part is differentiable off `s = 1`;
      O4.  `em_zeta_order_ext`       -- THE CONTINUATION: the order-`m` identity on `Re s > 1 - m`,
                                        `s ≠ 1` (identity theorem on the convex strip
                                        `1 - m < Re s < 1`, anchored at `s = 1/2`);
      O5.  `em_zeta_orderK_enclosure_ext`, `em_zeta_orderK_enclosure_odd_ext` -- the general-K
                                        remainder bounds of `EMZetaHigh` for `σ > 1 - 2K`,
                                        resp. `σ > -2K` (so `σ = -1` is covered from `K = 1` on).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin + analytic
    continuation); it says nothing about the Riemann Hypothesis.
-/


open MeasureTheory Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMOff

open EMHigh

/-! ## O1. The tail as a Mellin transform. -/

/-- The periodized Bernoulli function `B̃_m`, cut off to `(N, ∞)`, as a complex function. -/
noncomputable def sawCut (m N : ℕ) (x : ℝ) : ℂ :=
  Set.indicator (Ioi (N : ℝ)) (fun y : ℝ => (sawBernoulli m y : ℂ)) x



/-! ## O2. Differentiability of the tail on `Re s > 1 - m`. -/













/-! ## O3. Differentiability of the finite part off `s = 1`. -/



/-! ## O4. THE CONTINUATION of the order-`m` identity to `Re s > 1 - m`. -/



/-! ## O5. The general-K remainder bounds off the critical line. -/







end EMOff

end ZetaReflection


def ArdaRH65K_Turing121_EMZetaOfflineCore : Nat := 0


