-- Prove2me | Definitions.Def_TaoFivePrimes_RH114p5RoundedCoefficients
-- name    : TaoFivePrimes_RH114p5RoundedCoefficients
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:50:41.43535+00:00
-- url     : https://prove2.me/theorems/5ef3fb87-5df8-417e-bcc7-fc49c686a753
-- title:
--   Rounded xi coefficients at height 114.5
-- statement:
--   This list contains forty proposed integers $C_0,\ldots,C_{39}$ for the normalized local xi polynomial centered at $\tfrac12+114.5i$. The intended rational coefficient is $C_n/10^8$.
--
--   $$
--   P(s)=\sum_{n=0}^{39}\frac{C_n}{10^8}\bigl(-i(s-\tfrac12-114.5i)\bigr)^n.
--   $$
--
--   The list alone is numerical data; its translation accuracy and analytic meaning require separate proofs.
-- source:
--   Exact integer translation of the published 256 moment data and 48 extended candidate moments, using the local xi/Taylor framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The height-114.5 arithmetic data are new.

/- Proposed 40-term height-114.5 local xi coefficients at scale 10^37.
The moment data originate in the work of sometik179 and Gabewhigham. This
list alone is not an analytic approximation or a zero-location claim. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RH114p5RoundedCoefficients : List ℤ := [1779633140, 8246467194, -9119066605, 736373936, 1736786539, -574223868, -27782403, 45732886, -7636450, -396690, 285726, -29656, -1982, 724, -48, -4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


