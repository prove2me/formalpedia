-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_StripReprR1
-- name    : ArdaRH65K_Turing121_StripReprR1
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:56.358764+00:00
-- url     : https://prove2.me/theorems/172adef6-bb9b-4b33-b1c6-0a7e7d474f6f
-- title:
--   StripReprR1 certificate definitions
-- statement:
--   This bundle provides the auxiliary coefficients and complex powers for that strip representation. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{ZeroFreeBridge.cOne},\;\mathtt{ZeroFreeBridge.fPow}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zero_free_bridge/lean/StripReprR1.lean

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Mathlib
/- (R1) DISCHARGE for `zeta_fract_repr_of` -- THE HARD ONE, WORK IN PROGRESS.

   The fractional-part representation on `Re s > 1`:

       riemannZeta s = s/(s-1) - s · ∫_{x>1} {x} x^{-(s+1)} dx  =  stripRHS s.

   Mathlib v4.32.0 has NO such representation (confirmed), so it is built by Abel
   summation (`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) applied to
   `f x = x^{-s}`, `c 0 = 0`, `c (n+1) = 1`:

     ∑_{k≤n} k^{-s}  →  0 - ∫_{t>1} (-s·t^{-s-1})·⌊t⌋ dt  =  s∫_{t>1} ⌊t⌋ t^{-s-1} dt,
     ⌊t⌋ = t - {t},  s∫_{t>1} t^{-s} dt = s/(s-1)   ⟹   ζ(s) = s/(s-1) - s∫_{t>1}{t}t^{-s-1}.

   STATUS: FULLY ASSEMBLED, CI-green -- no `sorry`. The five analytic Abel-summation
   hypotheses (hf_diff, hf_int, h_lim, hg_dom, hg_int) are discharged on `Re s > 1`
   via a shared derivative helper `hasDerivAt_fPow` and the partial-sum `sum_cOne`;
   part (A) `tendsto_partialSum_zeta` identifies the LHS limit as `riemannZeta s`
   (Complex.summable_one_div_nat_cpow + zeta_eq_tsum... + hasSum_nat_add_iff reindex);
   part (B) evaluates the RHS limit value = `stripRHS s` (⌊t⌋ = t - {t} split,
   `∫_{Ioi 1}(↑t)^{-s} = 1/(s-1)` via integral_Ioi_cpow_of_lt). This discharges the
   R1 input of `zeta_fract_repr_of`. conjecture1_proved = False.
-/


open MeasureTheory Filter Topology Set

namespace ZeroFreeBridge

/-- Coefficients `c 0 = 0`, `c n = 1` for `n ≥ 1`. -/
 noncomputable def cOne : ℕ → ℂ := fun n => if n = 0 then 0 else 1

/-- The summand base `f x = x^{-s}`. -/
 noncomputable def fPow (s : ℂ) : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)











end ZeroFreeBridge


def ArdaRH65K_Turing121_StripReprR1 : Nat := 0


