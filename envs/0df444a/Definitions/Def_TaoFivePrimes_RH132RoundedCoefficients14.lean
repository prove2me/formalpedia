-- Prove2me | Definitions.Def_TaoFivePrimes_RH132RoundedCoefficients14
-- name    : TaoFivePrimes_RH132RoundedCoefficients14
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:51:03.255349+00:00
-- url     : https://prove2.me/theorems/1cef413d-2d81-4d8f-bd6e-c0db9f86bd43
-- title:
--   Candidate local xi coefficients at height 132
-- statement:
--   Store forty proposed integer numerators $c_0,\ldots,c_{39}$ with common denominator $10^{14}$ for a local polynomial at the center $1/2+132i$ and xi scale $10^{43}$:
--
--   $$
--   P(s)=\sum_{n=0}^{39}\frac{c_n}{10^{14}}
--   \left(-i\left(s-\frac12-132i\right)\right)^n.
--   $$
--
--   The list defines candidate arithmetic data. Agreement with the Riemann xi function and all zero-location conclusions require separate certified theorems.
-- source:
--   Candidate data from exact fixed-point oscillatory quadrature and the theta/Mellin framework due to sometik179 and Gabewhigham; no approximation is asserted by this definition.

/- Candidate 40-term height-132 local xi coefficients, denominator 10^14.
The Mellin/theta-jet framework is due to sometik179 and Gabewhigham. This list
alone asserts no analytic approximation or zeta-zero statement. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RH132RoundedCoefficients14 : List ℤ := [10489349699252497, -1953217368209016, -11242906415896704, 5783114711678385, 901734780847706, -1195999065171509, 219241457533295, 37269985057302, -19027315712187, 1792268698431, 332054528693, -92419271633, 4459050368, 1167536653, -193897521, 3482576, 1961056, -206609, -1143, 1787, -122, -3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


