-- Prove2me | Definitions.Def_PermBlockchain_Transfers_vendorCost
-- name    : PermBlockchain_Transfers_vendorCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:49.198766+00:00
-- url     : https://prove2.me/theorems/01b521a3-e0d5-48e2-847c-397bc21ce4c4
-- title:
--   Vendor costs $c_h(x)=\gamma x$ and $c_l$
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   The high vendor has linear cost $c_h(x)=\gamma x$ with $\gamma>0$; the low vendor has cost $c_l(x)$, strictly increasing and convex.
--
--   **Formalization Note** The properties of $c_l$ are hypotheses of the theorems (Assumption 1 and strict monotonicity), not part of this definition.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11); Appendix A, p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_Vert

namespace PermBlockchain.Transfers

/-- **Vendor production costs: `c_h(x) = γx` and `c_l(x)`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), §3.1, p. 10 (PDF p. 11): "We assume that c_h is linear, whereas c_l is strictly
increasing and convex"; Appendix A, p. 28 (PDF p. 29): "we assume c_h(x) = γx with γ > 0". -/
noncomputable def vendorCost (γ : ℝ) (cl : ℝ → ℝ) : Vert → ℝ → ℝ
  | .hi, x => γ * x
  | .lo, x => cl x

end PermBlockchain.Transfers


