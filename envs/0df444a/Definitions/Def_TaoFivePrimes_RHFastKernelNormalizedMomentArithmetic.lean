-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic
-- name    : TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T20:09:51.700437+00:00
-- url     : https://prove2.me/theorems/f587d670-18de-45c6-9ec4-d4f293c434c0
-- title:
--   Parameterized gamma record to normalized moment arithmetic
-- statement:
--   Ordinary integer rotation, eighth-power pair, denominator, and rounded normalized-moment algorithm for the parameterized gamma record. Same exact formulas as the accepted fixed-center normalized-moment program, with the public parameterized Record type. Asserts no numerical identity, approximation bound or RH.
-- source:
--   Platt Fourier construction DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHFastKernelMomentArithmetic
open RHFastKernelGammaArithmetic RHFastKernelLogData
noncomputable def rotate (z : Int×Int) (k : Nat) : Int×Int :=
  match k%4 with
  | 0 => z
  | 1 => (-z.2,z.1)
  | 2 => (-z.1,-z.2)
  | _ => (z.2,-z.1)
noncomputable def rawPair (v : Record) : Int×Int :=
  let w:=square (square (square ((v.cos:Int),(v.sin:Int))))
  ((v.amplitude:Int)*w.1,(v.amplitude:Int)*(if v.negative then -w.2 else w.2))
noncomputable def denominator (k : Nat) : Nat := D^9*(8192*10^50)^k*k.factorial
noncomputable def moment (i : Nat) (v : Record) (k : Nat) : Int×Int :=
  let z:=rotate (rawPair v) k
  let y : Int := -(P:Int)*((i:Int)-8192)
  (z.1*y^k*(2:Int)^80/(denominator k:Int),z.2*y^k*(2:Int)^80/(denominator k:Int))
end RHFastKernelMomentArithmetic
noncomputable def TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic : Nat := 26


