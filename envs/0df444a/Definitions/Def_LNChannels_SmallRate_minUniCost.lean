-- Prove2me | Definitions.Def_LNChannels_SmallRate_minUniCost
-- name    : LNChannels_SmallRate_minUniCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:57.64614+00:00
-- url     : https://prove2.me/theorems/a3c261cf-1cd9-497f-8443-a66307d6a700
-- title:
--   Minimal unidirectional channel cost
-- statement:
--   The optimal unidirectional cost is the infimum of the closed-form cost over positive real channel sizes:
--
--   $$c^{\mathrm{opt}}(0,\lambda)=\inf_{m>0}c^{0,m}(0,\lambda).$$
--
--   This quantity is the square-root benchmark in Theorem 3(i). **Formalization Note** The infimum does not itself assert attainment; theorem 3(i)'s size clause addresses a minimizer separately.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), pp. 6–7 (PDF 7–8), equations (1), (2), (7)

import Definitions.Def_LNChannels_Exact_uniCost

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- Minimal unidirectional cost over strictly positive real sizes. -/
noncomputable def minUniCost (lam r B : ℝ) : ℝ :=
  sInf (LNChannels.Exact.uniCost lam r B '' Set.Ioi 0)

end LNChannels.SmallRate


