-- Prove2me | Definitions.Def_TaoFivePrimes_RH128RoundedCoefficients14
-- name    : TaoFivePrimes_RH128RoundedCoefficients14
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:09:00.543216+00:00
-- url     : https://prove2.me/theorems/33f6a255-8ac7-4b60-a57b-a97eb025c70d
-- title:
--   Candidate local xi coefficients at height 128
-- statement:
--   This list records forty candidate integer numerators with denominator $10^{14}$ for a local polynomial centered at $1/2+128i$, after scaling xi by $10^{41}$. Agreement with the translated moment polynomial and the analytic approximation is proved separately.
-- source:
--   Exact translation of candidate Mellin moment data for the height-128 xi polynomial. The earlier theta-jet and Mellin framework is due to sometik179 and Gabewhigham; the additional rounded data and translation certificates are new.

/- Candidate 40-term height-128 local xi coefficients, denominator 10^14.
The Mellin-moment framework is due to sometik179 and Gabewhigham. This list
alone asserts no analytic approximation or zeta-zero statement. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RH128RoundedCoefficients14 : List ℤ := [1822089653616441, 1208661394385914, -4234978782195129, 2230944430329295, -77499244576973, -250525150271985, 67617807125192, 1859727359135, -3634808305247, 521456065566, 35833189720, -18139104656, 1488118081, 155478466, -39383109, 1830726, 287301, -43624, 965, 278, -27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


