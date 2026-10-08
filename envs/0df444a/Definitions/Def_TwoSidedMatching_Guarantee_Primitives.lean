-- Prove2me | Definitions.Def_TwoSidedMatching_Guarantee_Primitives
-- name    : TwoSidedMatching_Guarantee_Primitives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:35.241508+00:00
-- url     : https://prove2.me/theorems/90476cbc-696e-4b38-b45c-56a58ec53358
-- title:
--   Bridge to the published bilateral-trade environment
-- statement:
--   The distribution environment is the published `MechanismDesign.BilateralTrade.Environment`, reused under the local name `TwoSidedMatching.Guarantee.Environment` so the frozen shared market module can import it. Its density supports, cumulative distributions, virtual values and weak regularity condition are exactly the published definitions.
--
--   **Formalization Note** This is a name alias, with no new distribution assumptions or mathematical structure.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text pp. 8–11, Assumptions 1–2

import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

namespace TwoSidedMatching.Guarantee

/-- Bridge to the published bilateral-trade distribution environment. The shared
market module imports this name. -/
abbrev Environment := MechanismDesign.BilateralTrade.Environment

end TwoSidedMatching.Guarantee


