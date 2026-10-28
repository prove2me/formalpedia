-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
-- name    : TaoFivePrimes_RHExtendedMomentData304to319
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:29:33.058086+00:00
-- url     : https://prove2.me/theorems/17f7bff3-f5cd-44ff-96c6-800b52a20478
-- title:
--   Candidate scaled moments 304 through 319
-- statement:
--   This list stores proposed integer numerators $C_j$ for $304\le j\le319$, with intended denominator $10^{64}$. The list is numerical data; its agreement with the rational quadrature and the true Mellin moments is proved separately.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

/- Candidate scaled Mellin moment numerators for indices 304--319.
The underlying theta-jet data and Mellin method are due to sometik179, with
foundations by Gabewhigham. The list itself does not assert an enclosure. -/
import Mathlib.Data.Int.Basic
set_option autoImplicit false
@[noinline] def TaoFivePrimes_RHExtendedMomentData304to319 : List ℤ := [
  557607087617141274743206,
  93691311761939084187003,
  15660516044485978192682,
  2604087758336735378623,
  430779471272455605355,
  70894282435016304173,
  11607299811283010974,
  1890696752548185558,
  306400946237467450,
  49401791013789178,
  7924765720357970,
  1264818041680520,
  200851115451533,
  31734500995218,
  4988924613967,
  780380885814
]


