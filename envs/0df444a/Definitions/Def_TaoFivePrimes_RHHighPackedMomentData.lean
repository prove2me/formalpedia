-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighPackedMomentData
-- name    : TaoFivePrimes_RHHighPackedMomentData
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T00:05:22.821601+00:00
-- url     : https://prove2.me/theorems/983b8913-12af-4114-a72c-344c2b802e77
-- title:
--   Signed packed gamma-moment data decoder
-- statement:
--   Transparent decoder for26 signed complex dyadic moment pairs stored as52 offset96-bit integer fields. This data representation asserts no accuracy or RH result.
-- source:
--   Ordinary positional integer encoding for exact gamma-moment certificates in the Platt Fourier architecture, DOI10.1090/mcom/3198. Surrounding attribution: sometik179 c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
namespace RHHighPackedMoment
noncomputable def bits : Nat := 96
noncomputable def bias : Nat := 2^95
noncomputable def component (p j : Nat) : Int := ((p/2^(bits*j)%2^bits:Nat):Int)-(bias:Int)
noncomputable def decode (p k : Nat) : Int×Int := (component p (2*k),component p (2*k+1))
end RHHighPackedMoment
noncomputable def TaoFivePrimes_RHHighPackedMomentData : Nat := 96


