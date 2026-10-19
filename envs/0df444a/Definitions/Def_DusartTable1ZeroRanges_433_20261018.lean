-- Prove2me | Definitions.Def_DusartTable1ZeroRanges_433_20261018
-- name    : DusartTable1ZeroRanges_433_20261018
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-18T12:59:56.526356+00:00
-- url     : https://prove2.me/theorems/6e586ce0-b3e9-4b53-88ed-05f3ea2f8c89
-- title:
--   Positive and absolute zero ranges for explicit moment estimates
-- statement:
--   Let $\mathcal Z$ be the nontrivial zeros of the Riemann zeta function in the open critical strip. For a real cutoff $T$, these four subtypes represent
--
--   $$
--   \mathcal Z_{\ge}(T)=\{\rho\in\mathcal Z:T\le\operatorname{Im}\rho\},\qquad
--   \mathcal Z_{>}(T)=\{\rho\in\mathcal Z:T<\operatorname{Im}\rho\},
--   $$
--   $$
--   \mathcal Z_{|\cdot|>}(T)=\{\rho\in\mathcal Z:T<|\operatorname{Im}\rho|\},\qquad
--   \mathcal Z_{+,\le}(T)=\{\rho\in\mathcal Z:0<\operatorname{Im}\rho\le T\}.
--   $$
--
--   They keep endpoint conventions explicit in finite and infinite zero-moment estimates. For positive $T$, the first two ranges also consist of positive ordinates.
-- source:
--   Original complete Lean derivations recorded in dusart-table1-433, supporting TaoFivePrimes.dusart_table1_psi_bounds_for_log_four (8042dc39-d956-476c-a4d7-36d003a415aa). Numerical table: Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Table 1 and the explicit psi estimates, pp. 230–234, DOI 10.1007/s11139-016-9839-4. The additional bounds here are proved supporting variants, not quotations of unverified numerical inputs. Nonvanishing inputs are the accepted ExplicitPNT and TaoFivePrimes theorems and the accepted OAI.SevenEighths Hecke-to-zeta result. Abel summation and the complete smoothing definitions are reused from their published interfaces with their existing attribution.

import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum

set_option autoImplicit false
namespace ExplicitPNT.DusartTable1

abbrev HighPositiveZero (T : ℝ) :=
  {ρ : ℂ // DusartSmoothing.RvM.IsNontrivialZero ρ ∧ T ≤ ρ.im}

abbrev StrictHighPositiveZero (T : ℝ) :=
  {ρ : ℂ // DusartSmoothing.RvM.IsNontrivialZero ρ ∧ T < ρ.im}

abbrev StrictHighAbsoluteZero (T : ℝ) :=
  {ρ : ℂ // DusartSmoothing.RvM.IsNontrivialZero ρ ∧ T < |ρ.im|}

abbrev LowPositiveZero (T : ℝ) :=
  {ρ : ℂ // DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T}

end ExplicitPNT.DusartTable1


