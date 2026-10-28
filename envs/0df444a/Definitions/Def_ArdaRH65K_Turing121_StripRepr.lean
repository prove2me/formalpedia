-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_StripRepr
-- name    : ArdaRH65K_Turing121_StripRepr
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:25.923526+00:00
-- url     : https://prove2.me/theorems/b4310e33-b4df-47d9-a073-9aa066f0b3d1
-- title:
--   StripRepr certificate definitions
-- statement:
--   This bundle defines the fractional-part integral and associated representation on a complex strip. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ZeroFreeBridge.fractIntegrand},\;\mathtt{ZeroFreeBridge.fractIntegral},\;\mathtt{ZeroFreeBridge.stripRHS},\;\mathtt{ZeroFreeBridge.stripDomain}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/StripRepr.lean

import Mathlib
/- INPUT (R) FOR THE STRIP GROWTH BOUND: the fractional-part / Euler-Maclaurin representation
   of the Riemann zeta function on the half-plane Re s > 0,

       zeta(s) = s/(s-1) - s * integral_{x>1} {x} * x^{-(s+1)} dx        (Re s > 0, s != 1),

   where {x} = Int.fract x.  This is the piece `zeta_strip_bound_of` (in ZeroFreeBridge.lean)
   CONSUMES as its hypothesis `hrepr` (with I = the integral), and whose companion bound
   `zeta_repr_integral_bound` (input B) is already discharged there.  Assembling (R) closes the
   crude strip growth bound |zeta(sigma+it)| <= ||s||/||s-1|| + ||s||/sigma to a single unconditional
   input.  Crude growth only (~|t|); NOT the sharp |t|^{1-sigma} nor the log|t| that feeds the region,
   and the Vinogradov-Korobov rate needs VMVT (absent from Mathlib).  A gap-filler FEEDING Layer 2,
   NOT a proof of RH.  conjecture1_proved = False.

   PROOF ARCHITECTURE (5 steps):
     R1  identity on Re s > 1, via Abel summation (`sum_mul_eq_sub_integral_mul` +
         `tendsto_sum_mul_atTop_nhds_one_sub_integral`) applied to f(x) = x^{-s}, c = 1;
     R2  the RHS integral is complex-analytic in s on {Re s > 0} (differentiation under the integral);
     R3  the whole RHS s/(s-1) - s*I(s) is analytic on {0 < Re s} \ {1};
     R4  zeta is analytic on {s != 1};
     R5  identity theorem: both sides analytic on the preconnected open {0<Re s}\{1}, agree on the
         open subset {Re s > 1}, hence agree everywhere.

   This file FULLY ASSEMBLES R3/R4/R5 with NO `stub` and NO `postulate`.  The two genuinely-hard
   analytic inputs R1 and R2 are taken as explicit HYPOTHESES of the main theorem
   `zeta_fract_repr_of` -- exactly the style of `zeta_boundary_contradiction` and `zeta_strip_bound_of`
   in ZeroFreeBridge.lean, which likewise take their hard analytic limits/representations as
   hypotheses.  The convenience wrapper `zeta_fract_repr` (matching the requested signature) is then
   `zeta_fract_repr_of` fed the R1/R2 witnesses; those two witnesses are the remaining CI-iteration
   targets and their intended proofs are sketched in `zeta_fract_repr_gt`/`differentiableAt_fractIntegral`
   below (currently the only two declarations awaiting discharge, clearly delimited).

   RISK ORDER: R1 (Abel-summation identity) >> R5-preconnectedness > R2.  Uncertain Mathlib names
   are flagged inline with `-- FLAG:`.
-/

open scoped Real
open Filter Topology MeasureTheory

namespace ZeroFreeBridge

/-- The RHS integrand of the strip representation, as a function of the parameter `s`. -/
noncomputable def fractIntegrand (s : ℂ) (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ) / (x : ℂ) ^ (s + 1)

/-- The RHS integral `I(s) = ∫_{x>1} {x} · x^{-(s+1)} dx`. -/
noncomputable def fractIntegral (s : ℂ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ), fractIntegrand s x

/-- The RHS function `s ↦ s/(s-1) - s · I(s)`. -/
noncomputable def stripRHS (s : ℂ) : ℂ := s / (s - 1) - s * fractIntegral s

/-- The open right half-plane punctured at `1`. -/
def stripDomain : Set ℂ := {s : ℂ | 0 < s.re} \ {1}



  -- (1 : ℂ).re = 1 contradicts 1 < 1

/- ===================================================================================
   ASSEMBLED MAIN THEOREM (R3 + R4 + R5), taking R1 and R2 as hypotheses.  NO `stub`/`postulate`.
   =================================================================================== -/



/- ===================================================================================
   THREE REMAINING CI-ITERATION TARGETS — the hypotheses `zeta_fract_repr_of` consumes, to be
   discharged (each unblocks the fully-unconditional `zeta_fract_repr` matching the requested
   signature).  Kept as DOCUMENTED obligations, NOT `stub` stubs, to preserve the file's gap-free
   invariant.  Verified-present Mathlib API in brackets.

   (R1)  `∀ {z}, 1 < z.re → riemannZeta z = stripRHS z`  — the Abel-summation identity on Re s > 1.
         HARDEST.  Tools: `sum_mul_eq_sub_integral_mul`, `tendsto_sum_mul_atTop_nhds_one_sub_integral`
         (Mathlib.NumberTheory.AbelSummation), `zeta_eq_tsum_one_div_nat_add_one_cpow`,
         `Complex.deriv_cpow_const` (for `deriv (·^(-s)) = -s·(·)^(-s-1)` on `slitPlane`).
   (R2)  `∀ {z}, z ∈ stripDomain → DifferentiableAt ℂ fractIntegral z`  — differentiation under the
         integral.  Tool: `hasDerivAt_integral_of_dominated_loc_of_lip` (7 hyps), parameter-derivative
         `-{x}·(log x)·x^{-(s+1)}`, dominated by `x^{-(σ₀-ε)-1}·log x`; base integrability
         `integrableOn_Ioi_norm_cpow_of_lt {a : ℂ} (ha : a.re < -1) (hc : 0 < c)` with `a = -(s+1)`.
   (R3)  `IsPreconnected stripDomain`  — the punctured open right half-plane.  Tool: cover by the four
         convex pieces `{0<re, im>0}`, `{0<re, im<0}`, `{0<re, re<1}`, `{re>1}` (each `Convex.isPreconnected`)
         chained by `IsPreconnected.union` on their overlaps.

   `zeta_fract_repr_of` FULLY ASSEMBLES R4 (`analyticOn_riemannZeta.mono`) + R3-analyticity of the RHS
   (`DifferentiableOn.analyticOnNhd`) + R5 (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`), no
   stub/postulate, given (R1)(R2)(R3) — exactly the conditional-hypothesis style of `zeta_boundary_contradiction`
   and `zeta_strip_bound_of`.  conjecture1_proved = False.
   =================================================================================== -/

end ZeroFreeBridge


def ArdaRH65K_Turing121_StripRepr : Nat := 0


