-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
-- name    : InfoBargaining_SellerPayoff_FocalPrior_costDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:52.334819+00:00
-- url     : https://prove2.me/theorems/a316da47-a8f3-469c-9b72-5a6d16246e18
-- title:
--   Admissible seller costs for each focal prior
-- statement:
--   The seller's cost is positive ("$c>0$", p. 6) and trade is potentially desirable, $c\in(\underline u,\bar u)$, where $[\underline u,\bar u]$ is the support of the prior (p. 7). The admissible costs $\{c>0\}\cap(\underline u,\bar u)$ are therefore
--
--   1. $(0,1)$ for the uniform and the modified pareto priors (support $[0,1]$);
--   2. $(0,\infty)$ for the exponential prior (support $[0,\infty)$);
--   3. $(0,\infty)$ for the logistic prior (support $\mathbb R$; the bound $c>0$ comes from p. 6).
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §2, unnumbered, p. 6 ("c > 0") and p. 7 ("c ∈ (u̲, ū)")

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior

namespace InfoBargaining.SellerPayoff

/-- **The admissible seller costs for each focal prior.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022):
the cost is positive ("c > 0", §2, p. 6) and "Trade is potentially desirable, i.e.,
c ∈ (u̲, ū)" (§2, p. 7), where `[u̲, ū]` is the support of the prior.

The domain is `{c > 0} ∩ (u̲, ū)`:
* `uniform`, `modPareto`: support `[0, 1]`, domain `(0, 1)`;
* `exponential`: support `[0, ∞)`, domain `(0, ∞)`;
* `logistic`: support `(−∞, ∞)`, domain `(0, ∞)` (from `c > 0`). -/
def FocalPrior.costDomain : FocalPrior → Set ℝ
  | .uniform => Set.Ioo 0 1
  | .exponential _ _ => Set.Ioi 0
  | .logistic _ _ => Set.Ioi 0
  | .modPareto _ _ => Set.Ioo 0 1

end InfoBargaining.SellerPayoff


