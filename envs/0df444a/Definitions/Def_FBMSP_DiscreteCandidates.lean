-- Prove2me | Definitions.Def_FBMSP_DiscreteCandidates
-- name    : FBMSP_DiscreteCandidates
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T04:52:55.264509+00:00
-- url     : https://prove2.me/theorems/00113848-9018-40e3-8537-a5591ea4b5e0
-- title:
--   Nonnegative realized valuations as finite candidate prices
-- statement:
--   For a rational finite market, the candidate set is zero together with all nonnegative realized valuation breakpoints $\mu_i+e_j$. This definition only constructs the set; the associated theorem must prove that its cardinality is at most $nm+1$ and that restricting prices to it loses no revenue.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Appendix C, p.50 (ec16); Remark 3, p.18.

import Definitions.Def_FBMSP_Hardness

namespace FBMSP

/-- The zero outside option together with every nonnegative realized
valuation in a finite rational market.  This definition does not restrict the
original policy's prices: those may still be arbitrary nonnegative reals. -/
noncomputable def rationalCandidatePrices (I : RationalMarketInput) : Finset ℝ := by
  classical
  exact insert 0
    (((I.means.toFinset.product I.shocks.toFinset).image
      (fun z : ℚ × ℚ => ((z.1 + z.2 : ℚ) : ℝ))).filter (fun p => 0 ≤ p))

end FBMSP


