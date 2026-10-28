-- Prove2me | Definitions.Def_TaoFivePrimes_RH110p5RoundedCoefficients
-- name    : TaoFivePrimes_RH110p5RoundedCoefficients
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:18:09.473263+00:00
-- url     : https://prove2.me/theorems/2816a0ef-35b0-479b-acf9-ad3961bfe3a3
-- title:
--   Rounded xi coefficients at height 110.5
-- statement:
--   This list contains forty proposed integers $C_0,\ldots,C_{39}$ for the normalized local xi polynomial centered at $\tfrac12+110.5i$. The intended rational coefficient is $C_n/10^8$.
--
--   $$
--   P(s)=\sum_{n=0}^{39}\frac{C_n}{10^8}\bigl(-i(s-\tfrac12-110.5i)\bigr)^n.
--   $$
--
--   The list alone is numerical data; its translation accuracy and analytic meaning require separate proofs.
-- source:
--   Exact integer translation of the published 256 moment data and 16 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-110.5 arithmetic data are new.

/- Proposed 40-term height-110.5 local xi coefficients at scale 10^36.
The moment data originate in the work of sometik179 and Gabewhigham. This
list alone is not an analytic approximation or a zero-location claim. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RH110p5RoundedCoefficients : List ℤ := [-11324433668, 36413939477, -33269416540, 8301293668, 2609274993, -1732779271, 216976066, 56432388, -20071742, 1275856, 384273, -81364, 2519, 1053, -146, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


