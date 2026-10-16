-- Prove2me | Definitions.Def_LNChannels_SmallRate_minSymCost
-- name    : LNChannels_SmallRate_minSymCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:03.322534+00:00
-- url     : https://prove2.me/theorems/b74f5a8a-3dc1-4345-bf60-e30d33067d57
-- title:
--   Minimal symmetric bidirectional channel cost
-- statement:
--   At equal payment rates $\lambda$, the optimal bidirectional cost is the infimum over both positive real commitments:
--
--   $$c^{\mathrm{opt}}(\lambda,\lambda)=\inf_{l_1,l_2>0}c^{l_1,l_2}(\lambda,\lambda).$$
--
--   The cube-root law of Theorem 3(ii) concerns this two-variable optimum. **Formalization Note** No minimizing pair is chosen or assumed to exist in this definition.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), pp. 6–7 (PDF 7–8), equations (3), (8)

import Definitions.Def_LNChannels_RateBounds_ClosedForms

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- Minimal symmetric bidirectional cost over strictly positive real sizes. -/
noncomputable def minSymCost (lam r B : ℝ) : ℝ :=
  sInf {x | ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ LNChannels.RateBounds.biCost lam lam r B l₁ l₂ = x}

end LNChannels.SmallRate


